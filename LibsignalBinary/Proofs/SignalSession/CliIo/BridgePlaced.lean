/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Spec
public import VerifiedLibraries.RustStd.Proofs.MallocngInst
public import LibsignalBinary.Heap.Iface
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.SignalSession.CliIo.ReadHookAlign

/-!
# Placed `mallocng` Bridge for `signal_session_io::{read_stdin, read_file}`

Instantiates `cliIoReadStdin_ok` and `cliIoReadFileGen_ok` (`cliIoReadFile_ok`, `cliIoReadFileRo_ok`)
over `cliIoMallocngAllocAt J γ A tp brkStart`, splitting and re-absorbing `StdErrnoCell s0.tpidrEl0`
inside the heap invariant and aligning postconditions to `ioVecAt (cliIoMallocngAllocAt ...).repAlloc`
with `CliIoFilesOomPreserved` on out-of-memory exits.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.CliIo.BridgePlaced

open Arm64 Arm64.Obj Arm64.Process ProofLib.StdStartup
open ProofLib hiding MallocngAddrs MallocngIface
open CryptoVerification (signalSessionIoMultiLib)
open CryptoVerification.SignalSession (PathOk pathComps)
open CryptoVerification.SignalSession.CliExt (stdinBytes ioVecAt bytesAt)
open VerifiedLibraries.Mallocng (
  MallocngAddrs MallocngBudget MallocngEnv MallocngIface MallocngIfaceFacts
)
open VerifiedLibraries.Musl (
  memcpySrc muslErrnoLocationSpec
)
open VerifiedLibraries.RustStd (
  RustStdAlloc RustStdAllocAddrs RustStdAllocEntries
  StdErrnoCell OomPreserved AllocSeqFits cPathOf
  allocAllocShimSpec rustStdAllocSpec rustStdDeallocSpec rustStdReallocSpec
  mallocngRustCliAllocOf mallocngRustCliPoolOf_sep_stdErrnoCell_eq
)
open LibsignalBinary.Heap (RustCliAlloc RustLayoutOk)
open LibsignalBinary.Proofs.SignalSession.CliIo.Sym (
  CliIoBlockNoExtern
  cliIoReadStdinSym cliIoReadFileSym cliIoOpenSym cliIoReadSym cliIoCloseSym
  cliIoErrnoLocationSym cliIoMemcpySym
  cliIoRustAllocSym cliIoRustReallocSym cliIoRustDeallocSym cliIoRustNoAllocShimSym
)
open LibsignalBinary.Proofs.SignalSession.CliIo.MuslDirReadClose (
  muslReadDir32Spec muslClose48LocalSpec
)
open LibsignalBinary.Proofs.SignalSession.CliIo.MuslReadStdin (
  muslReadStdin32Spec muslReadFileOrStdio32Spec
)
open LibsignalBinary.Proofs.SignalSession.CliIo.MuslOpenDeterministic (
  classifyOpenRdonly muslOpenRdonlyDetSpec
)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadLoopCommon (
  ExternPreservesOracleSymtab cliIoStdinCap cliIoFileCap
)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadStdinProof (
  CliIoCallPreserved cliIoReadStdinSpec cliIoReadStdin_ok
)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileProof (
  cliIoReadFileGenSpec cliIoReadFileGen_ok
)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadHookAlign (
  stdinBytes_eq_some_iff cliIoStdinLoopResult_entails_ok cliIoStdinLoopResult_entails_overCap
  cliIoReadFileExpected cliIoReadFileResult_entails_ioVecAt
)

/-! ## 1. `cliIoMallocngAllocAt` (`module`-Clean Alias of `mallocngRustCliAllocAt`) & Helpers -/

/-- `module`-compatible definition of `mallocngPoolAt` (definitionally equal to
    `LibsignalBinary.Heap.MallocngBridge.mallocngPoolAt`). -/
def cliIoMallocngPoolAt (J : MallocngIface) (γ : GhostName) (A : MallocngAddrs)
    (tp brkStart : BitVec 64) (s : State) : SepProp :=
  ∃∗ b : MallocngBudget, ∃∗ ivs : List (BitVec 64 × Nat),
    MallocngEnv J γ A tp brkStart b ivs s

/-- `module`-compatible definition of `mallocngLive` (definitionally equal to
    `LibsignalBinary.Heap.MallocngBridge.mallocngLive`). -/
def cliIoMallocngLive (J : MallocngIface) (γ : GhostName) (p : BitVec 64)
    (n align : Nat) : SepProp :=
  J.Block γ p n ∗ ⌜p ≠ 0#64 ∧ align ∣ p.toNat ∧ 16 ∣ p.toNat ∧ p.toNat + n < 2 ^ 64⌝

/-- `module`-compatible `RustCliAlloc` backed by `VerifiedLibraries.Mallocng` (`rfl`-equal to
    `LibsignalBinary.Heap.mallocngRustCliAllocAt`). -/
def cliIoMallocngAllocAt (J : MallocngIface) (γ : GhostName) (A : MallocngAddrs)
    (tp brkStart : BitVec 64) : RustCliAlloc where
  pool := cliIoMallocngPoolAt J γ A tp brkStart
  live := fun p n al => cliIoMallocngLive J γ p n al ∗ ⌜RustLayoutOk n al⌝
  block_valid := by
    intro p n al
    unfold cliIoMallocngLive
    rw [sepConj_comm (J.Block γ p n ∗ _) ⌜RustLayoutOk n al⌝,
      sepConj_comm (J.Block γ p n) ⌜_⌝]
    refine Entails.pure_left fun hlo => ?_
    refine Entails.pure_left fun ⟨hne, hdvd, hd16, hlt⟩ => ?_
    exact Entails.pure_right ⟨hne, Nat.mod_eq_zero_of_dvd hdvd, hlt, hlo⟩
      (Entails.pure_right hlo
        (Entails.pure_right ⟨hne, hdvd, hd16, hlt⟩ (Entails.refl (J.Block γ p n))))
  pool_transport := by
    rintro s s' ⟨hbs, hb, ht⟩
    simp only [cliIoMallocngPoolAt, MallocngEnv, hbs, hb, ht]

theorem allocSeqFits_mallocngRustCliAllocOf {J : MallocngIface} (hIf : MallocngIfaceFacts J)
    (γ : GhostName) (A : MallocngAddrs) (align : Nat) :
    ∀ (lb lk : Nat) (caps : List Nat),
      AllocSeqFits (mallocngRustCliAllocOf J hIf γ A) align lb lk caps
  | _, _, [] => trivial
  | _, _, c :: cs => ⟨trivial, go_true _ _ c cs⟩
where
  go_true : ∀ (lb lk prev : Nat) (cs : List Nat),
      AllocSeqFits.go (mallocngRustCliAllocOf J hIf γ A) align lb lk prev cs
    | _, _, _, [] => trivial
    | _, _, _, c' :: cs' => ⟨trivial, go_true _ _ c' cs'⟩

private theorem rustLayoutOk_of_std {size align : Nat}
    (h : VerifiedLibraries.RustStd.RustLayoutOk size align) :
    RustLayoutOk size align :=
  ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩

theorem stdLive_entails_repLive {J : MallocngIface} (hIf : MallocngIfaceFacts J)
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart : BitVec 64)
    (p : BitVec 64) (n al : Nat) :
    (mallocngRustCliAllocOf J hIf γ A).live p n al ⊢
      (cliIoMallocngAllocAt J γ A tp brkStart).repAlloc.live p n al := by
  change (⌜p.toNat % al = 0 ∧ VerifiedLibraries.RustStd.RustLayoutOk n al⌝ ∗ J.Block γ p n) ⊢
    (cliIoMallocngLive J γ p n al ∗ ⌜RustLayoutOk n al⌝)
  refine Entails.pure_left fun ⟨hmod, hlay⟩ => ?_
  refine Entails.trans (hIf.block_nonnull γ p n) ?_
  refine Entails.pure_left fun ⟨hpNe, h16, hBound48, _⟩ => ?_
  have hBound64 : p.toNat + n < 2 ^ 64 := Nat.lt_of_le_of_lt hBound48 (by decide)
  unfold cliIoMallocngLive
  have hEq :
      (J.Block γ p n ∗ ⌜p ≠ 0#64 ∧ al ∣ p.toNat ∧ 16 ∣ p.toNat ∧ p.toNat + n < 2 ^ 64⌝) ∗
        ⌜RustLayoutOk n al⌝ =
      ⌜RustLayoutOk n al⌝ ∗
        (⌜p ≠ 0#64 ∧ al ∣ p.toNat ∧ 16 ∣ p.toNat ∧ p.toNat + n < 2 ^ 64⌝ ∗ J.Block γ p n) := by
    sep_ac_rfl
  rw [hEq]
  exact Entails.pure_right (rustLayoutOk_of_std hlay)
    (Entails.pure_right ⟨hpNe, Nat.dvd_of_mod_eq_zero hmod, h16, hBound64⟩ (Entails.refl _))

theorem pool_split_errno {J : MallocngIface} (hIf : MallocngIfaceFacts J)
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart : BitVec 64) (s : State) :
    (cliIoMallocngAllocAt J γ A tp brkStart).pool s ⊢
      ⌜s.tpidrEl0 = tp ∧ s.brkStart = brkStart⌝ ∗
        (StdErrnoCell s.tpidrEl0 ∗ (mallocngRustCliAllocOf J hIf γ A).pool 0 0 s) := by
  change cliIoMallocngPoolAt J γ A tp brkStart s ⊢ _
  unfold cliIoMallocngPoolAt VerifiedLibraries.Mallocng.MallocngEnv
  refine Entails.sepExists_elim fun b => Entails.sepExists_elim fun ivs => ?_
  refine Entails.pure_left fun ⟨htp, hbs⟩ => ?_
  refine Entails.pure_right ⟨htp, hbs⟩ ?_
  rw [sepConj_comm (StdErrnoCell s.tpidrEl0),
    mallocngRustCliPoolOf_sep_stdErrnoCell_eq hIf γ A 0 0 s, htp, hbs]
  exact Entails.sepExists_right b (Entails.sepExists_right ivs (Entails.refl _))

theorem pool_reabsorb_errno {J : MallocngIface} (hIf : MallocngIfaceFacts J)
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart : BitVec 64) (lb' lk' : Nat)
    {s0 sf : State} (htp0 : s0.tpidrEl0 = tp) (hbs0 : s0.brkStart = brkStart)
    (hpres : CliIoCallPreserved s0 sf) :
    (mallocngRustCliAllocOf J hIf γ A).pool lb' lk' sf ∗ StdErrnoCell s0.tpidrEl0 ⊢
      (cliIoMallocngAllocAt J γ A tp brkStart).pool sf := by
  have htp_sf : sf.tpidrEl0 = tp := hpres.2.2.1.trans htp0
  have hbs_sf : sf.brkStart = brkStart := hpres.2.2.2.1.trans hbs0
  have htp_eq : s0.tpidrEl0 = sf.tpidrEl0 := htp0.trans htp_sf.symm
  rw [htp_eq, mallocngRustCliPoolOf_sep_stdErrnoCell_eq hIf γ A lb' lk' sf]
  change _ ⊢ cliIoMallocngPoolAt J γ A tp brkStart sf
  unfold cliIoMallocngPoolAt VerifiedLibraries.Mallocng.MallocngEnv
  refine Entails.sepExists_mono fun b => Entails.sepExists_mono fun ivs => ?_
  rw [htp_sf, hbs_sf]
  exact Entails.pure_right ⟨rfl, rfl⟩ (Entails.refl _)

/-! ## 2. `mallocng`-Backed `read_stdin` Contract & Discharge -/

/-- Out-of-memory invariant preserved across `read_stdin` and `read_file`: `files`, `trace`, and
    `sigActions` are all unchanged (`fd 0` offset or temporary local `fd` may have advanced). -/
def CliIoFilesOomPreserved (s0 sf : State) : Prop :=
  sf.fs.files = s0.fs.files ∧ sf.trace = s0.trace ∧ sf.sigActions = s0.sigActions

/-- Placed `mallocng`-backed Hoare contract for `signal_session_io::read_stdin` (no separate
    `StdErrnoCell` required; `ioVecAt` output; exact `2^20` cap semantics). -/
def cliIoMallocngReadStdinSpec {J : MallocngIface} (γ : GhostName) (A : MallocngAddrs)
    (tp brkStart : BitVec 64) (stackBytes : Nat) :
    Spec (BitVec 64 × List (BitVec 8)) where
  pre := fun (sret, bs) s0 =>
    ⌜4256 + Rust.hookStack ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64 ∧
      stackBytes ≤ s0.sp.toNat ∧ s0.sp.toNat ≤ Arm64.USER_VA_LIMIT ∧
      s0.readReg64 .x8 = sret ∧ stdinBytes s0.fs = some bs⌝ ∗
      (stackAt s0.sp stackBytes ∗ memRegion sret 24 ∗
        (cliIoMallocngAllocAt J γ A tp brkStart).pool s0)
  post := fun (sret, bs) s0 sf =>
    let r : Except Unit (List (BitVec 8)) :=
      if bs.length ≤ cliIoStdinCap then .ok bs else .error ()
    ⌜CliIoCallPreserved s0 sf ∧ sf.fs.files = s0.fs.files⌝ ∗
      (stackAt s0.sp stackBytes ∗
        ioVecAt (cliIoMallocngAllocAt J γ A tp brkStart).repAlloc sret r ∗
        (cliIoMallocngAllocAt J γ A tp brkStart).pool sf)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ s0 sf => ⌜CliIoFilesOomPreserved s0 sf⌝

theorem cliIoMallocngReadStdin_ok {J : MallocngIface} (hIf : MallocngIfaceFacts J)
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart : BitVec 64)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program} {stackBytes : Nat}
    (hsvc : P.svc = Syscall.standard)
    (hext_os : ExternPreservesOracleSymtab P)
    (hext0 : CliIoBlockNoExtern mpl P 0)
    (hext4 : CliIoBlockNoExtern mpl P 4)
    (hread : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadStdin32Spec)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoMemcpySym)
      stdMemcpySpec)
    (hshim : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym)
      allocAllocShimSpec)
    (hAlloc : RustStdAllocEntries (mallocngRustCliAllocOf J hIf γ A) P
      { alloc   := signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym
        dealloc := signalSessionIoMultiLib.resolve mpl cliIoRustDeallocSym
        realloc := signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym }) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadStdinSym)
      (signalSessionIoMultiLib.withCodeLoaded mpl
        (cliIoMallocngReadStdinSpec (J := J) γ A tp brkStart stackBytes)) := by
  have hraw := cliIoReadStdin_ok (mallocngRustCliAllocOf J hIf γ A) hpl
    (stackBytes := stackBytes) hsvc hext_os hext0 hext4 hread hmemcpy hshim
    hAlloc.alloc hAlloc.realloc hAlloc.dealloc
  apply subroutine_ok_outcome_intro
  rintro ⟨sret, bs⟩ R s0 hpc hrun hpre hsp
  dsimp only [MultiPlacedLib.withCodeLoaded, cliIoMallocngReadStdinSpec] at hpre
  rw [sepConj_comm _ ⌜signalSessionIoMultiLib.CodeLoaded mpl s0.mem⌝, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hlo, hhi, hsp_lo, hsp_va, hx8, hstdin⟩, hmem⟩
  obtain ⟨d0, hd0, hkind, hcan, hdrop⟩ := stdinBytes_eq_some_iff.mp hstdin
  have hmem1 := Satisfies.mono (sepConj_mono_left
    (sepConj_mono_right (sepConj_mono_right (pool_split_errno hIf γ A tp brkStart s0)))) hmem
  have hEqPre :
      (stackAt s0.sp stackBytes ∗ memRegion sret 24 ∗
        (⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗
          (StdErrnoCell s0.tpidrEl0 ∗ (mallocngRustCliAllocOf J hIf γ A).pool 0 0 s0))) ∗ R =
      ⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗
        ((stackAt s0.sp stackBytes ∗ memRegion sret 24 ∗ StdErrnoCell s0.tpidrEl0 ∗
          (mallocngRustCliAllocOf J hIf γ A).pool 0 0 s0) ∗ R) := by sep_ac_rfl
  rw [hEqPre, satisfies_pure_sepConj] at hmem1
  rcases hmem1 with ⟨⟨htp0, hbs0⟩, hmem2⟩
  have hfits := allocSeqFits_mallocngRustCliAllocOf hIf γ A 1 0 0
    (ReadLoopCommon.cliIoReadCaps 8 (s0.fs.stdin.drop d0.offset).length)
  have hpre_raw : s0.mem ⊨
      (signalSessionIoMultiLib.withCodeLoaded mpl
        (cliIoReadStdinSpec (mallocngRustCliAllocOf J hIf γ A) stackBytes)).pre
          (sret, d0, 0, 0) s0 ∗ R := by
    dsimp only [MultiPlacedLib.withCodeLoaded, cliIoReadStdinSpec]
    rw [sepConj_comm _ ⌜signalSessionIoMultiLib.CodeLoaded mpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hlo, hhi, hsp_lo, hsp_va, hx8, hd0, hkind, hcan, hfits⟩, hmem2⟩
  apply hraw.mono_outcome (sret, d0, 0, 0) R s0 hpc hrun hpre_raw hsp
  intro sf hout
  rcases hout with ⟨hret, hcs, hpost⟩ | ⟨hpan, hp⟩ | ⟨code, hex, he⟩ | ⟨hoom_st, hoom⟩
  · refine Or.inl ⟨hret, hcs, ?_⟩
    dsimp only [MultiPlacedLib.withCodeLoaded, cliIoMallocngReadStdinSpec]
    dsimp only [MultiPlacedLib.withCodeLoaded, cliIoReadStdinSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hpres, hpost⟩
    have hlive := stdLive_entails_repLive hIf γ A tp brkStart
    by_cases hcap : bs.length ≤ cliIoStdinCap
    · simp only [hcap, ↓reduceIte]
      have hpost1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
        (cliIoStdinLoopResult_entails_ok (mallocngRustCliAllocOf J hIf γ A)
          (cliIoMallocngAllocAt J γ A tp brkStart).repAlloc hlive
          sret d0 0 0 s0 sf hdrop hcap)))) hpost
      let pp := VerifiedLibraries.RustStd.allocSeqPool (mallocngRustCliAllocOf J hIf γ A) 1 0 0
        (ReadLoopCommon.cliIoReadCaps 8 bs.length)
      have hEq1 :
          (stackAt s0.sp stackBytes ∗
            (⌜sf.fs = s0.fs.setFd 0#64 (some { d0 with offset := d0.offset + bs.length }) ∧
              sf.fs.files = s0.fs.files⌝ ∗
              ioVecAt (cliIoMallocngAllocAt J γ A tp brkStart).repAlloc sret (.ok bs) ∗
              (mallocngRustCliAllocOf J hIf γ A).pool pp.1 pp.2 sf) ∗
            StdErrnoCell s0.tpidrEl0) ∗ R =
          ⌜sf.fs = s0.fs.setFd 0#64 (some { d0 with offset := d0.offset + bs.length }) ∧
            sf.fs.files = s0.fs.files⌝ ∗
            ((stackAt s0.sp stackBytes ∗
              ioVecAt (cliIoMallocngAllocAt J γ A tp brkStart).repAlloc sret (.ok bs) ∗
              ((mallocngRustCliAllocOf J hIf γ A).pool pp.1 pp.2 sf ∗ StdErrnoCell s0.tpidrEl0)) ∗ R) := by
        sep_ac_rfl
      rw [hEq1, satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨⟨_, hfiles⟩, hpost2⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hpres, hfiles⟩, Satisfies.mono (sepConj_mono_left (sepConj_mono_right
        (sepConj_mono_right (pool_reabsorb_errno hIf γ A tp brkStart pp.1 pp.2 htp0 hbs0 hpres)))) hpost2⟩
    · have hover : cliIoStdinCap < bs.length := Nat.lt_of_not_ge hcap
      simp only [hcap, ↓reduceIte]
      have hpost1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
        (cliIoStdinLoopResult_entails_overCap (mallocngRustCliAllocOf J hIf γ A)
          (cliIoMallocngAllocAt J γ A tp brkStart).repAlloc
          sret d0 0 0 s0 sf hdrop hover)))) hpost
      have hEq1 :
          (stackAt s0.sp stackBytes ∗
            (⌜sf.fs = s0.fs.setFd 0#64 (some { d0 with offset := d0.offset + (cliIoStdinCap + 1) }) ∧
              sf.fs.files = s0.fs.files⌝ ∗
              ioVecAt (cliIoMallocngAllocAt J γ A tp brkStart).repAlloc sret (.error ()) ∗
              (mallocngRustCliAllocOf J hIf γ A).pool 0 0 sf) ∗
            StdErrnoCell s0.tpidrEl0) ∗ R =
          ⌜sf.fs = s0.fs.setFd 0#64 (some { d0 with offset := d0.offset + (cliIoStdinCap + 1) }) ∧
            sf.fs.files = s0.fs.files⌝ ∗
            ((stackAt s0.sp stackBytes ∗
              ioVecAt (cliIoMallocngAllocAt J γ A tp brkStart).repAlloc sret (.error ()) ∗
              ((mallocngRustCliAllocOf J hIf γ A).pool 0 0 sf ∗ StdErrnoCell s0.tpidrEl0)) ∗ R) := by
        sep_ac_rfl
      rw [hEq1, satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨⟨_, hfiles⟩, hpost2⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hpres, hfiles⟩, Satisfies.mono (sepConj_mono_left (sepConj_mono_right
        (sepConj_mono_right (pool_reabsorb_errno hIf γ A tp brkStart 0 0 htp0 hbs0 hpres)))) hpost2⟩
  · dsimp only [MultiPlacedLib.withCodeLoaded, cliIoReadStdinSpec] at hp
    rw [satisfies_pure_sepConj] at hp; exact False.elim hp.1
  · dsimp only [MultiPlacedLib.withCodeLoaded, cliIoReadStdinSpec] at he
    rw [satisfies_pure_sepConj] at he; exact False.elim he.1
  · refine Or.inr (Or.inr (Or.inr ⟨hoom_st, ?_⟩))
    dsimp only [MultiPlacedLib.withCodeLoaded, cliIoMallocngReadStdinSpec]
    dsimp only [MultiPlacedLib.withCodeLoaded, cliIoReadStdinSpec,
      ReadStdinLoop.cliIoStdinOom] at hoom
    rw [satisfies_pure_sepConj] at hoom ⊢
    rcases hoom with ⟨⟨k, sm, _, ⟨htr_m, hsig_m⟩, hfs_m, ⟨hfs_f, htr_f, hsig_f⟩⟩, hR⟩
    refine ⟨⟨?_, htr_f.trans htr_m, hsig_f.trans hsig_m⟩, hR⟩
    rw [hfs_f, hfs_m]; rfl

/-! ## 3. `mallocng`-Backed `read_file` Contract & Discharge -/

theorem memcpySrc_eq_bytesAt (ro : Bool) (p : BitVec 64) (bs : List (BitVec 8)) :
    memcpySrc ro p bs = bytesAt ro p bs := by
  cases ro <;> rfl

/-- Placed `mallocng`-backed Hoare contract for `signal_session_io::read_file(path: &str)`
    (`ro = false` for `↦ₛ`, `ro = true` for `↦ᵣ`; no separate `StdErrnoCell` required;
    `ioVecAt` output; exact `4096`-B path and `2^21`-B file cap semantics). -/
def cliIoMallocngReadFileGenSpec (ro : Bool) {J : MallocngIface} (γ : GhostName)
    (A : MallocngAddrs) (tp brkStart : BitVec 64) (stackBytes : Nat) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (sret, pathPtr, pathBytes) s0 =>
    ⌜8432 + Rust.hookStack ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64 ∧
      stackBytes ≤ s0.sp.toNat ∧ s0.sp.toNat ≤ Arm64.USER_VA_LIMIT ∧
      s0.readReg64 .x0 = pathPtr ∧ (s0.readReg64 .x1).toNat = pathBytes.length ∧
      s0.readReg64 .x8 = sret ∧ s0.fs.allocFd ≠ none ∧
      (pathBytes.length < 4096 → 0#8 ∉ pathBytes →
        PathOk (cPathOf pathBytes) = true ∧
          ((pathComps (cPathOf pathBytes)).all fun c => decide (c.length ≤ NAME_MAX)) = true)⌝ ∗
      (stackAt s0.sp stackBytes ∗ bytesAt ro pathPtr pathBytes ∗
        memRegion sret 24 ∗ (cliIoMallocngAllocAt J γ A tp brkStart).pool s0)
  post := fun (sret, pathPtr, pathBytes) s0 sf =>
    let r := cliIoReadFileExpected s0.fs.files pathBytes
    ⌜CliIoCallPreserved s0 sf ∧ sf.fs = s0.fs⌝ ∗
      (stackAt s0.sp stackBytes ∗ bytesAt ro pathPtr pathBytes ∗
        ioVecAt (cliIoMallocngAllocAt J γ A tp brkStart).repAlloc sret r ∗
        (cliIoMallocngAllocAt J γ A tp brkStart).pool sf)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ s0 sf => ⌜CliIoFilesOomPreserved s0 sf⌝

abbrev cliIoMallocngReadFileSpec {J : MallocngIface} (γ : GhostName) (A : MallocngAddrs)
    (tp brkStart : BitVec 64) (stackBytes : Nat) :=
  cliIoMallocngReadFileGenSpec false (J := J) γ A tp brkStart stackBytes

abbrev cliIoMallocngReadFileRoSpec {J : MallocngIface} (γ : GhostName) (A : MallocngAddrs)
    (tp brkStart : BitVec 64) (stackBytes : Nat) :=
  cliIoMallocngReadFileGenSpec true (J := J) γ A tp brkStart stackBytes

theorem cliIoMallocngReadFileGen_ok (ro : Bool) {J : MallocngIface} (hIf : MallocngIfaceFacts J)
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart : BitVec 64)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program} {stackBytes : Nat}
    (hsvc : P.svc = Syscall.standard)
    (hext_os : ExternPreservesOracleSymtab P)
    (hext3 : CliIoBlockNoExtern mpl P 3)
    (hext4 : CliIoBlockNoExtern mpl P 4)
    (hopen : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoOpenSym)
      muslOpenRdonlyDetSpec)
    (herrno : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoErrnoLocationSym)
      muslErrnoLocationSpec)
    (hread_dir : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadDir32Spec)
    (hread_file : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadFileOrStdio32Spec)
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoCloseSym)
      muslClose48LocalSpec)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoMemcpySym)
      stdMemcpySpec)
    (hshim : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym)
      allocAllocShimSpec)
    (hAlloc : RustStdAllocEntries (mallocngRustCliAllocOf J hIf γ A) P
      { alloc   := signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym
        dealloc := signalSessionIoMultiLib.resolve mpl cliIoRustDeallocSym
        realloc := signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym }) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadFileSym)
      (signalSessionIoMultiLib.withCodeLoaded mpl
        (cliIoMallocngReadFileGenSpec ro (J := J) γ A tp brkStart stackBytes)) := by
  have hraw := cliIoReadFileGen_ok ro (mallocngRustCliAllocOf J hIf γ A) hpl
    (stackBytes := stackBytes) hsvc hext_os hext3 hext4 hopen herrno hread_dir hread_file
    hclose hmemcpy hshim hAlloc.alloc hAlloc.realloc hAlloc.dealloc
  apply subroutine_ok_outcome_intro
  rintro ⟨sret, pathPtr, pathBytes⟩ R s0 hpc hrun hpre hsp
  dsimp only [MultiPlacedLib.withCodeLoaded, cliIoMallocngReadFileGenSpec] at hpre
  rw [sepConj_comm _ ⌜signalSessionIoMultiLib.CodeLoaded mpl s0.mem⌝, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hlo, hhi, hsp_lo, hsp_va, hx0, hx1, hx8, hallocFd, hpathOk⟩, hmem⟩
  rw [← memcpySrc_eq_bytesAt ro pathPtr pathBytes] at hmem
  have hmem1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (pool_split_errno hIf γ A tp brkStart s0))))) hmem
  have hEqPre :
      (stackAt s0.sp stackBytes ∗ memcpySrc ro pathPtr pathBytes ∗ memRegion sret 24 ∗
        (⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗
          (StdErrnoCell s0.tpidrEl0 ∗ (mallocngRustCliAllocOf J hIf γ A).pool 0 0 s0))) ∗ R =
      ⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗
        ((stackAt s0.sp stackBytes ∗ memcpySrc ro pathPtr pathBytes ∗ memRegion sret 24 ∗
          StdErrnoCell s0.tpidrEl0 ∗ (mallocngRustCliAllocOf J hIf γ A).pool 0 0 s0) ∗ R) := by
    sep_ac_rfl
  rw [hEqPre, satisfies_pure_sepConj] at hmem1
  rcases hmem1 with ⟨⟨htp0, hbs0⟩, hmem2⟩
  have hfits : ∀ fd bs, pathBytes.length < 4096 → 0#8 ∉ pathBytes →
      classifyOpenRdonly s0.fs (cPathOf pathBytes) = .ok fd .localFile →
      s0.fs.files (cPathOf pathBytes) = some (.file bs) →
      AllocSeqFits (mallocngRustCliAllocOf J hIf γ A) 1 0 0 (ReadLoopCommon.cliIoReadCaps 9 bs.length) :=
    fun _ bs _ _ _ _ => allocSeqFits_mallocngRustCliAllocOf hIf γ A 1 0 0
      (ReadLoopCommon.cliIoReadCaps 9 bs.length)
  have hpre_raw : s0.mem ⊨
      (signalSessionIoMultiLib.withCodeLoaded mpl
        (cliIoReadFileGenSpec ro (mallocngRustCliAllocOf J hIf γ A) stackBytes)).pre
          (sret, pathPtr, pathBytes, 0, 0) s0 ∗ R := by
    dsimp only [MultiPlacedLib.withCodeLoaded, cliIoReadFileGenSpec]
    rw [sepConj_comm _ ⌜signalSessionIoMultiLib.CodeLoaded mpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hlo, hhi, hsp_lo, hsp_va, hx0, hx1, hx8, hpathOk, hfits⟩, hmem2⟩
  apply hraw.mono_outcome (sret, pathPtr, pathBytes, 0, 0) R s0 hpc hrun hpre_raw hsp
  intro sf hout
  rcases hout with ⟨hret, hcs, hpost⟩ | ⟨hpan, hp⟩ | ⟨code, hex, he⟩ | ⟨hoom_st, hoom⟩
  · refine Or.inl ⟨hret, hcs, ?_⟩
    dsimp only [MultiPlacedLib.withCodeLoaded, cliIoMallocngReadFileGenSpec]
    dsimp only [MultiPlacedLib.withCodeLoaded, cliIoReadFileGenSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hpres, hpost⟩
    rw [memcpySrc_eq_bytesAt ro pathPtr pathBytes] at hpost
    have hlive := stdLive_entails_repLive hIf γ A tp brkStart
    have hpost1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (cliIoReadFileResult_entails_ioVecAt
        (mallocngRustCliAllocOf J hIf γ A) (cliIoMallocngAllocAt J γ A tp brkStart).repAlloc
        hlive sret pathBytes 0 0 s0 sf hallocFd))))) hpost
    cases hr : cliIoReadFileExpected s0.fs.files pathBytes with
    | ok bs =>
      simp only [hr] at hpost1
      let pp := VerifiedLibraries.RustStd.allocSeqPool (mallocngRustCliAllocOf J hIf γ A) 1 0 0
        (ReadLoopCommon.cliIoReadCaps 9 bs.length)
      have hEq1 :
          (stackAt s0.sp stackBytes ∗ bytesAt ro pathPtr pathBytes ∗
            (⌜sf.fs = s0.fs⌝ ∗
              ioVecAt (cliIoMallocngAllocAt J γ A tp brkStart).repAlloc sret (.ok bs) ∗
              (mallocngRustCliAllocOf J hIf γ A).pool pp.1 pp.2 sf) ∗
            StdErrnoCell s0.tpidrEl0) ∗ R =
          ⌜sf.fs = s0.fs⌝ ∗
            ((stackAt s0.sp stackBytes ∗ bytesAt ro pathPtr pathBytes ∗
              ioVecAt (cliIoMallocngAllocAt J γ A tp brkStart).repAlloc sret (.ok bs) ∗
              ((mallocngRustCliAllocOf J hIf γ A).pool pp.1 pp.2 sf ∗ StdErrnoCell s0.tpidrEl0)) ∗ R) := by
        sep_ac_rfl
      rw [hEq1, satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨hfs_eq, hpost2⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hpres, hfs_eq⟩, Satisfies.mono (sepConj_mono_left (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right
          (pool_reabsorb_errno hIf γ A tp brkStart pp.1 pp.2 htp0 hbs0 hpres))))) hpost2⟩
    | error u =>
      cases u
      simp only [hr] at hpost1
      have hEq1 :
          (stackAt s0.sp stackBytes ∗ bytesAt ro pathPtr pathBytes ∗
            (⌜sf.fs = s0.fs⌝ ∗
              ioVecAt (cliIoMallocngAllocAt J γ A tp brkStart).repAlloc sret (.error ()) ∗
              (mallocngRustCliAllocOf J hIf γ A).pool 0 0 sf) ∗
            StdErrnoCell s0.tpidrEl0) ∗ R =
          ⌜sf.fs = s0.fs⌝ ∗
            ((stackAt s0.sp stackBytes ∗ bytesAt ro pathPtr pathBytes ∗
              ioVecAt (cliIoMallocngAllocAt J γ A tp brkStart).repAlloc sret (.error ()) ∗
              ((mallocngRustCliAllocOf J hIf γ A).pool 0 0 sf ∗ StdErrnoCell s0.tpidrEl0)) ∗ R) := by
        sep_ac_rfl
      rw [hEq1, satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨hfs_eq, hpost2⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hpres, hfs_eq⟩, Satisfies.mono (sepConj_mono_left (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right
          (pool_reabsorb_errno hIf γ A tp brkStart 0 0 htp0 hbs0 hpres))))) hpost2⟩
  · dsimp only [MultiPlacedLib.withCodeLoaded, cliIoReadFileGenSpec] at hp
    rw [satisfies_pure_sepConj] at hp; exact False.elim hp.1
  · dsimp only [MultiPlacedLib.withCodeLoaded, cliIoReadFileGenSpec] at he
    rw [satisfies_pure_sepConj] at he; exact False.elim he.1
  · refine Or.inr (Or.inr (Or.inr ⟨hoom_st, ?_⟩))
    dsimp only [MultiPlacedLib.withCodeLoaded, cliIoMallocngReadFileGenSpec]
    dsimp only [MultiPlacedLib.withCodeLoaded, cliIoReadFileGenSpec,
      ReadFileProof.cliIoReadFileOom] at hoom
    rw [satisfies_pure_sepConj] at hoom ⊢
    rcases hoom with ⟨⟨_, _, fd, _, k, sm, _, ⟨htr_m, hsig_m⟩, hfs_m, ⟨hfs_f, htr_f, hsig_f⟩⟩, hR⟩
    refine ⟨⟨?_, htr_f.trans htr_m, hsig_f.trans hsig_m⟩, hR⟩
    rw [hfs_f, hfs_m]; rfl

theorem cliIoMallocngReadFile_ok {J : MallocngIface} (hIf : MallocngIfaceFacts J)
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart : BitVec 64)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program} {stackBytes : Nat}
    (hsvc : P.svc = Syscall.standard)
    (hext_os : ExternPreservesOracleSymtab P)
    (hext3 : CliIoBlockNoExtern mpl P 3)
    (hext4 : CliIoBlockNoExtern mpl P 4)
    (hopen : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoOpenSym)
      muslOpenRdonlyDetSpec)
    (herrno : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoErrnoLocationSym)
      muslErrnoLocationSpec)
    (hread_dir : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadDir32Spec)
    (hread_file : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadFileOrStdio32Spec)
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoCloseSym)
      muslClose48LocalSpec)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoMemcpySym)
      stdMemcpySpec)
    (hshim : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym)
      allocAllocShimSpec)
    (hAlloc : RustStdAllocEntries (mallocngRustCliAllocOf J hIf γ A) P
      { alloc   := signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym
        dealloc := signalSessionIoMultiLib.resolve mpl cliIoRustDeallocSym
        realloc := signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym }) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadFileSym)
      (signalSessionIoMultiLib.withCodeLoaded mpl
        (cliIoMallocngReadFileSpec (J := J) γ A tp brkStart stackBytes)) :=
  cliIoMallocngReadFileGen_ok false hIf γ A tp brkStart hpl hsvc hext_os hext3 hext4
    hopen herrno hread_dir hread_file hclose hmemcpy hshim hAlloc

theorem cliIoMallocngReadFileRo_ok {J : MallocngIface} (hIf : MallocngIfaceFacts J)
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart : BitVec 64)
    {mpl : MultiPlacement} (hpl : signalSessionIoMultiLib.Placeable mpl)
    {P : Program} {stackBytes : Nat}
    (hsvc : P.svc = Syscall.standard)
    (hext_os : ExternPreservesOracleSymtab P)
    (hext3 : CliIoBlockNoExtern mpl P 3)
    (hext4 : CliIoBlockNoExtern mpl P 4)
    (hopen : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoOpenSym)
      muslOpenRdonlyDetSpec)
    (herrno : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoErrnoLocationSym)
      muslErrnoLocationSpec)
    (hread_dir : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadDir32Spec)
    (hread_file : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadSym)
      muslReadFileOrStdio32Spec)
    (hclose : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoCloseSym)
      muslClose48LocalSpec)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoMemcpySym)
      stdMemcpySpec)
    (hshim : subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoRustNoAllocShimSym)
      allocAllocShimSpec)
    (hAlloc : RustStdAllocEntries (mallocngRustCliAllocOf J hIf γ A) P
      { alloc   := signalSessionIoMultiLib.resolve mpl cliIoRustAllocSym
        dealloc := signalSessionIoMultiLib.resolve mpl cliIoRustDeallocSym
        realloc := signalSessionIoMultiLib.resolve mpl cliIoRustReallocSym }) :
    subroutine_ok P (signalSessionIoMultiLib.resolve mpl cliIoReadFileSym)
      (signalSessionIoMultiLib.withCodeLoaded mpl
        (cliIoMallocngReadFileRoSpec (J := J) γ A tp brkStart stackBytes)) :=
  cliIoMallocngReadFileGen_ok true hIf γ A tp brkStart hpl hsvc hext_os hext3 hext4
    hopen herrno hread_dir hread_file hclose hmemcpy hshim hAlloc

/-! ## 4. Schedule Identity with `SpecBudget.cliIoReadScheduleCaps` -/

theorem cliIoCap_eq (j : Nat) :
    LibsignalBinary.Heap.SpecBudget.cliIoCap j = ReadLoopCommon.cliIoCap j :=
  rfl

theorem cliIoCapIdx_eq : ∀ (K r : Nat),
    LibsignalBinary.Heap.SpecBudget.cliIoCapIdx K r = ReadLoopCommon.cliIoCapIdx K r
  | 0, _ => rfl
  | K + 1, r => by
    unfold LibsignalBinary.Heap.SpecBudget.cliIoCapIdx ReadLoopCommon.cliIoCapIdx
    rw [cliIoCap_eq, cliIoCapIdx_eq K r]

/-- Schedule equality between `SpecBudget.cliIoReadScheduleCaps` and
    `ReadLoopCommon.cliIoReadCaps`. -/
theorem cliIoReadScheduleCaps_eq_cliIoReadCaps (K r : Nat) :
    LibsignalBinary.Heap.SpecBudget.cliIoReadScheduleCaps K r =
      ReadLoopCommon.cliIoReadCaps K r := by
  have hfn : LibsignalBinary.Heap.SpecBudget.cliIoCap = ReadLoopCommon.cliIoCap := rfl
  unfold LibsignalBinary.Heap.SpecBudget.cliIoReadScheduleCaps ReadLoopCommon.cliIoReadCaps
  rw [hfn, cliIoCapIdx_eq K r]

end LibsignalBinary.Proofs.SignalSession.CliIo.BridgePlaced
