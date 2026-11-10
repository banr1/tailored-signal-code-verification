/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
public import LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.Startup
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Inst
public import ProofLib.ProgramReflection
public meta import ProofLib.ProgramReflection
import Arm64.Trusted.Spec.SepLogic

/-!
# Concrete Startup Framing, `F3CodeOk`, and `CliElfF3B2NeedLocksAssumptions`

Establishes `F3CodeOk` (`KeepsFrozen`-stable code and read-only invariant bundling
`LibsignalCodeRoLoaded`, `mallocngLib.CodeLoaded`, and `f3TrialRxProg.CodeLoaded` with
`MemExecFrozen`) on `patchElfTokensPlacedAt mpl cliElfImage`, frames `cliStaticsPlacedAt mpl`
across `musl` startup and exit, and discharges `CliElfF3B2NeedLocksAssumptions` for arbitrary
`LinkedAt cliElfBytes` placements `(mpl, mmpl)`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 400000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.StdStartup
open CryptoVerification (LibsignalFrozen LibsignalRoLoaded lsLogFilterSym)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (tokenName tokenStorageName)
open CryptoVerification.SignalSession
  (CliHooks Inputs cliElfBytes cliElfImage cliElf_parse cliElf_staticOk
   cliExternsPlaced cliProcessInputs libsignalSessionLib patchElfByte patchRegionByte processInputs)
open CryptoVerification.SignalSession.Cli
  (CliInputsOk ElfStaticOk InputsLoadable cliInputs)
open CryptoVerification.SignalSession.Cli.MainHops (cliMainStk)
open CryptoVerification.SignalSession.Coins (coinsLeftSym coinsNextSym)
open CryptoVerification.SignalSession.InitStack
  (cliStackSize cliStrs loadState_cli_layout sp0 stackBase toNat_sp0)
open CryptoVerification.SignalSession.MuslElf (SegSlice)
open CryptoVerification.SignalSession.Placed (cliProgPlacedSig cliTokenPatchPlaced)
open LibsignalBinary.Heap (BudgetLimits)
open LibsignalBinary.Heap.Fine
  (CliElfMallocngLayout StartupVmPreserved f3MallocngMpl f3SegByteSum f3SegCount f3StdLayout
   fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
  (CliElfF3B2NeedLocksAssumptions MuslHarnessFineNeedLocksGuardedPerInput
   MuslHarnessFineNeedLocksPerInput StdMainEntryLr cliBudgetLimits
   muslHarnessFineNeedLocksGuardedPerInput_of_startup)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
  (CliElfTokenCellsPlacedAt cliElfMallocngLayout_iff_patchElfTokensPlacedAt cliProgExtPlacedAt
   cliProgExtPlacedSigAt_cliExternsPlaced_eq cliStackShape_cliProcessInputs cliStaticsPlacedAt
   codeLoaded_cliProgExtPlaced_of_codeRoLoaded coinsStaticsPlacedAt
   externAt?_cliProgExtPlacedSigAt_eq_none loadState_patchElfTokensPlacedAt lsLogOffAt
   patchElfTokensPlacedAt tokenInitPlacedAtMpl)
open LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.Startup
  (F3StartupCode argvAtRO cStrAtRO f3StartupExtraChunks f3StartupMainPre
   f3StartupMainPreNeedLocks f3StartupResidual steps_lift_setTidOnly)
open LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.TlsZero
  (F3BssGlobals F3DataGlobals F3InitGlobals F3LayoutImageFacts F3RoConstants F3TlsState
   extractF3LayoutImageFacts f3AllRwAtoms f3AllRwAtoms_sep_eq f3BssAtoms f3CheckRoSegment
   f3CheckRwSegment f3DataNoStderrAtoms f3MatchesImage f3MatchesImage_codeLoaded
   f3MatchesImage_satisfies_roConstants f3MatchesImage_segments f3SetTidOnlySvc
   f3StaticInitTlsSpec f3StaticInitTls_setTidOnly_ok)
open VerifiedLibraries.Mallocng
  (MallocngAddrs MallocngAuxvAt MallocngBrkStartWf mallocngAddrsOfPlacement)
open VerifiedLibraries.Mallocng.Proofs (mallocngMultiL)

/-! ## `MemExecFrozen`, `F3CodeInv`, and `F3CodeOk` -/

/-- Every executable byte in `m` is read-only (`r = true ∧ w = false`). -/
def MemExecFrozen (m : Memory) : Prop :=
  ∀ a : BitVec 64, (m.perm a).x = true → (m.perm a).r = true ∧ (m.perm a).w = false

theorem MemExecFrozen.of_perm_eq {m m' : Memory} (h : MemExecFrozen m)
    (hp : ∀ a : BitVec 64, m'.perm a = m.perm a) : MemExecFrozen m' := by
  intro a hx
  rw [hp a] at hx ⊢
  exact h a hx

/-- `KeepsFrozen`-stable two-placement code and read-only data invariant. -/
structure F3CodeInv (mpl mmpl : Obj.MultiPlacement) (m : Memory) : Prop where
  lsRo : LibsignalCodeRoLoaded mpl m
  mngCode : VerifiedLibraries.mallocngLib.CodeLoaded mmpl m
  rxCode : Tie.f3TrialRxProg.CodeLoaded m
  fromLoad : ∃ (inputs : ProcessInputs) (sLoad : State),
    (patchElfTokensPlacedAt mpl cliElfImage).loadState inputs = .ok sLoad ∧
      sLoad.mem.KeepsFrozen m

theorem F3CodeInv.of_keepsFrozen {mpl mmpl : Obj.MultiPlacement} {m m' : Memory}
    (h : F3CodeInv mpl mmpl m) (hkf : m.KeepsFrozen m') : F3CodeInv mpl mmpl m' where
  lsRo := h.lsRo.of_keepsFrozen hkf
  mngCode := h.mngCode.of_keepsFrozen hkf
  rxCode := h.rxCode.of_keepsFrozen hkf
  fromLoad :=
    let ⟨inputs, sLoad, hload, hkf0⟩ := h.fromLoad
    ⟨inputs, sLoad, hload, hkf0.trans hkf⟩

theorem F3CodeInv.mngBlockCodeLoaded {mpl mmpl : Obj.MultiPlacement} {m : Memory}
    (h : F3CodeInv mpl mmpl m) (j : Nat) (hj : j < VerifiedLibraries.mallocngLib.blocks.length)
    (ext ovr : String → Option (State → State)) (svc : State → State) :
    (VerifiedLibraries.mallocngLib.blockProgram mmpl j ext ovr svc).CodeLoaded m := by
  have hc := h.mngCode j hj
  exact Program.CodeLoaded.intro hc.aligned hc.no_wrap fun i hi =>
    ⟨hc.byte_eq i hi, hc.perm_eq i hi, hc.isLazyFree_eq i hi⟩

/-- Combined `F3CodeInv` and `MemExecFrozen` invariant for `CliElfF3B2NeedLocksAssumptions`. -/
def F3CodeOk (mpl mmpl : Obj.MultiPlacement) (m : Memory) : Prop :=
  F3CodeInv mpl mmpl m ∧ MemExecFrozen m

theorem f3CodeOk_of_keepsFrozen_and_perm {mpl mmpl : Obj.MultiPlacement} {m m' : Memory}
    (h : F3CodeOk mpl mmpl m) (hkf : m.KeepsFrozen m')
    (hp : ∀ a : BitVec 64, m'.perm a = m.perm a) : F3CodeOk mpl mmpl m' :=
  ⟨h.1.of_keepsFrozen hkf, h.2.of_perm_eq hp⟩

/-! ## Patched ELF, Token Cells, and `mallocngAddrsOfPlacement` Uniqueness -/

/-- Token-patched `cliElfImage` at canonical placement `f3LsMpl`. -/
noncomputable def f3PatchedElf : ElfImage :=
  patchElfTokensPlacedAt ElfCodeMatchesPlaced.f3LsMpl cliElfImage

theorem f3PatchedElf_eq_of_linkedAt {mpl : Obj.MultiPlacement}
    (hls : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    patchElfTokensPlacedAt mpl cliElfImage = f3PatchedElf := by
  have hst := ElfCodeMatchesPlaced.f3CliElf_statics_rho_eq_of_linkedAt hls
  unfold f3PatchedElf patchElfTokensPlacedAt
  rw [hst.2.2.2.1, hst.2.2.2.2]

set_option maxRecDepth 4000000 in
theorem f3PatchedElf_matchesImage : f3MatchesImage f3StdLayout f3PatchedElf = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
private theorem f3PatchedElf_rxSeg_eq :
    f3PatchedElf.segments[f3StdLayout.rxSegIdx]? = cliElfImage.segments[f3StdLayout.rxSegIdx]? := by
  rfl_kernel

theorem f3PatchedElf_rxProgram_eq :
    f3StdLayout.rxProgram f3PatchedElf = Tie.f3TrialRxProg := by
  have h1 : f3StdLayout.rxProgram f3PatchedElf = f3StdLayout.rxProgram cliElfImage := by
    unfold StdBinaryLayout.rxProgram
    rw [f3PatchedElf_rxSeg_eq]
  exact h1

private theorem cliElf_seg3_lt : 3 < cliElfImage.segments.length := by
  rw [Fixture.f3TrialElf_seg_count]
  decide

set_option maxRecDepth 4000000 in
private theorem cliElf_seg3_perm :
    (cliElfImage.segments[3]'cliElf_seg3_lt).perm = Perm.rw := by
  rfl_kernel

private noncomputable def f3Seg3Off (a : BitVec 64) : Nat :=
  (a - (cliElfImage.segments[3]'cliElf_seg3_lt).start).toNat

private def f3BytesEq : List (BitVec 8) → List (BitVec 8) → Bool
  | _, [] => true
  | [], _ :: _ => false
  | x :: xs, y :: ys => (x == y) && f3BytesEq xs ys

private theorem f3BytesEq_take_eq :
    ∀ (xs ys : List (BitVec 8)), f3BytesEq xs ys = true → xs.take ys.length = ys
  | _, [], _ => by simp
  | [], _ :: _, h => Bool.noConfusion h
  | x :: xs, y :: ys, h => by
    simp only [f3BytesEq, Bool.and_eq_true, beq_iff_eq] at h
    simp only [List.length_cons, List.take_succ_cons, h.1, f3BytesEq_take_eq xs ys h.2]

private theorem rawSeg3_slice_of_bytesEq1 (a : BitVec 64) (bs : List (BitVec 8))
    (ha : a = (cliElfImage.segments[3]'cliElf_seg3_lt).start + BitVec.ofNat 64 (f3Seg3Off a))
    (heq : f3BytesEq
      (Arm64.Process.fastDrop (f3Seg3Off a) (cliElfImage.segments[3]'cliElf_seg3_lt).bytes) bs = true) :
    SegSlice cliElfImage a bs Perm.rw := by
  refine ⟨3, cliElf_seg3_lt, f3Seg3Off a, cliElf_seg3_perm, ha, ?_⟩
  have h := f3BytesEq_take_eq _ bs heq
  rwa [Arm64.Process.fastDrop_eq_drop] at h

set_option maxRecDepth 4000000 in
/-- `CliElfTokenCellsPlacedAt mpl cliElfImage` holds for any `LinkedAt cliElfBytes mpl`. -/
theorem cliElf_tokenCellsPlacedAt_of_linkedAt {mpl : Obj.MultiPlacement}
    (hls : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    CliElfTokenCellsPlacedAt mpl cliElfImage := by
  have hst := ElfCodeMatchesPlaced.f3CliElf_statics_rho_eq_of_linkedAt hls
  refine { storage := ?_, once := ?_ }
  · rw [hst.2.2.2.1]
    exact rawSeg3_slice_of_bytesEq1 _ [255#8] (by rfl_kernel) (by rfl_kernel)
  · rw [hst.2.2.2.2]
    exact rawSeg3_slice_of_bytesEq1 _ [3#8, 0#8, 0#8, 0#8] (by rfl_kernel) (by rfl_kernel)

set_option maxRecDepth 4000000 in
private theorem mmpl_rho_eq_f3_of_chk {mmpl : Obj.MultiPlacement}
    (hmng : VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl) (s : String)
    (hchk : (mallocngMultiL.names.contains s &&
      (Obj.lookupBlockSym s VerifiedLibraries.mallocngLib.blocks == none)) = true := by rfl_kernel) :
    mmpl.ρ s = f3MallocngMpl.ρ s := by
  simp only [Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at hchk
  exact (ElfCodeMatchesPlaced.f3CliElf_mallocng_linkedAt_unique hmng).2.2.1 s hchk.1 hchk.2

set_option maxRecDepth 4000000 in
theorem mallocngAddrsOfPlacement_eq_f3_of_linkedAt {mmpl : Obj.MultiPlacement}
    (hmng : VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl) :
    mallocngAddrsOfPlacement mmpl = Inst.f3MAddrs := by
  unfold Inst.f3MAddrs mallocngAddrsOfPlacement
  exact congr (congr (congr (congr (congr (congr (congr (congr (congr (congr
    (congrArg VerifiedLibraries.Mallocng.MallocngAddrs.mk
      ((ElfCodeMatchesPlaced.f3CliElf_mallocng_linkedAt_unique hmng).1 0 (by decide)))
    (mmpl_rho_eq_f3_of_chk hmng _))
    (mmpl_rho_eq_f3_of_chk hmng _))
    (mmpl_rho_eq_f3_of_chk hmng _))
    (mmpl_rho_eq_f3_of_chk hmng _))
    (mmpl_rho_eq_f3_of_chk hmng _))
    (mmpl_rho_eq_f3_of_chk hmng _))
    (mmpl_rho_eq_f3_of_chk hmng _))
    (mmpl_rho_eq_f3_of_chk hmng _))
    (mmpl_rho_eq_f3_of_chk hmng _))
    (mmpl_rho_eq_f3_of_chk hmng _)

theorem f3StdExtra_entails_mallocngDataInit_of_linkedAt {mmpl : Obj.MultiPlacement}
    (hmng : VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl) :
    StdExtraRo f3StdLayout ∗ StdExtraRw f3StdLayout ⊢
      VerifiedLibraries.mallocngLib.dataInit mmpl ∗ Inst.f3MallocngRoPad := by
  have hEq : VerifiedLibraries.mallocngLib.dataInit mmpl =
      VerifiedLibraries.mallocngLib.dataInit f3MallocngMpl := by
    rw [VerifiedLibraries.Mallocng.Proofs.mallocngLib_dataInit_eq mmpl,
      VerifiedLibraries.Mallocng.Proofs.mallocngLib_dataInit_eq f3MallocngMpl,
      mallocngAddrsOfPlacement_eq_f3_of_linkedAt hmng]
  rw [hEq]
  exact Inst.f3StdExtra_entails_mallocngDataInit

/-! ## `F3CodeOk` on Patched ELF Load -/

private noncomputable def f3LsRoLo : Nat :=
  (cliElfImage.segments.getD f3StdLayout.roSegIdx { start := 0#64, perm := .ro, bytes := [] }).start.toNat

private noncomputable def f3LsRoHi : Nat :=
  (cliElfImage.segments.getD (f3StdLayout.roSegIdx + 1) { start := 0#64, perm := .ro, bytes := [] }).start.toNat

private def regionPermRoInWindow (lo hi : Nat) (r : Snapshot.Region) : Bool :=
  (r.perm == Perm.ro) ||
    (Nat.ble (r.start.toNat + r.bytes.length) (2 ^ 48) &&
      (Nat.ble (r.start.toNat + r.bytes.length) lo || Nat.ble hi r.start.toNat))

private theorem cellAt_perm_ro_of_window {lo hi : Nat} {a : BitVec 64} {p : Perm} {b : BitVec 8}
    (ha : lo ≤ a.toNat ∧ a.toNat < hi) :
    ∀ {rs : List Snapshot.Region},
      rs.all (regionPermRoInWindow lo hi) = true →
      Snapshot.cellAt rs a = some (some p, b) →
      p = Perm.ro
  | [], _, hc => by simp [Snapshot.cellAt] at hc
  | r :: tl, hwin, hc => by
    simp only [List.all_cons, Bool.and_eq_true] at hwin
    obtain ⟨hr, htl⟩ := hwin
    by_cases hlt : (a - r.start).toNat < r.bytes.length
    · rw [Obj.Interned.cellAt_cons_hit hlt] at hc
      injection hc with h1
      injection h1 with hp _
      injection hp with hperm
      subst hperm
      simp only [regionPermRoInWindow, Bool.or_eq_true, Bool.and_eq_true,
        beq_iff_eq, Nat.ble_eq] at hr
      rcases hr with hro | ⟨hub, hdisj⟩
      · exact hro
      · have hadd : (a - r.start) + r.start = a := BitVec.sub_add_cancel a r.start
        have hlt64 : (a - r.start).toNat + r.start.toNat < 2 ^ 64 := by omega
        have htonat : a.toNat = (a - r.start).toNat + r.start.toNat := by
          have h := congrArg BitVec.toNat hadd
          rw [BitVec.toNat_add, Nat.mod_eq_of_lt hlt64] at h
          exact h.symm
        omega
    · rw [Obj.Interned.cellAt_cons_miss (Nat.le_of_not_lt hlt)] at hc
      exact cellAt_perm_ro_of_window ha htl hc

set_option maxRecDepth 4000000 in
private theorem cliElf_segments_ro_window :
    cliElfImage.segments.all (regionPermRoInWindow f3LsRoLo f3LsRoHi) = true := by
  suffices h :
      (cliElfImage.segments.all fun r =>
        (r.perm == Perm.ro) ||
          withForcedNat (Arm64.Process.fastLen512 4096 r.bytes) fun len =>
            Nat.ble (r.start.toNat + len) (2 ^ 48) &&
              (Nat.ble (r.start.toNat + len) f3LsRoLo || Nat.ble f3LsRoHi r.start.toNat)) = true by
    rw [List.all_eq_true] at h ⊢
    intro r hr
    simpa only [regionPermRoInWindow, withForcedNat_eq, Arm64.Process.fastLen512_eq_length]
      using h r hr
  rfl_kernel

set_option maxRecDepth 4000000 in
private theorem f3LsSymAddrs_len_lt_2pow20 :
    ElfCodeMatchesData.f3LsSymAddrs.length < 2 ^ 20 := by
  have h : Nat.blt ElfCodeMatchesData.f3LsSymAddrs.length (2 ^ 20) = true := by rfl_kernel
  exact Nat.blt_eq.mp h

set_option maxRecDepth 4000000 in
private theorem ls_rodata_in_window :
    (ElfCodeMatchesData.lsInternedMultiLib.data.all fun d =>
      !d.readOnly ||
        (let a := (ElfCodeMatchesData.f3LsSymAddrs.getD d.sym 0#64).toNat
         Nat.ble f3LsRoLo a && Nat.ble (a + d.bytes.length + d.zeroTail) f3LsRoHi &&
           Nat.blt f3LsRoHi (2 ^ 64))) = true := by
  suffices h :
      (Obj.Interned.withVecTree 0#64 ElfCodeMatchesData.f3LsSymAddrs fun tAddr =>
        ElfCodeMatchesData.lsInternedMultiLib.data.all fun d =>
          !d.readOnly ||
            withForcedNat (tAddr.getD 0#64 d.sym).toNat fun a =>
              withForcedNat (Arm64.Process.fastLen512 4096 d.bytes) fun len =>
                Nat.ble f3LsRoLo a && Nat.ble (a + len + d.zeroTail) f3LsRoHi &&
                  Nat.blt f3LsRoHi (2 ^ 64)) = true by
    rw [Obj.Interned.withVecTree_eq, List.all_eq_true] at h
    rw [List.all_eq_true]
    intro d hd
    simpa only [withForcedNat_eq, Arm64.Process.fastLen512_eq_length,
      Obj.Interned.toVecTree_getD_all 0#64 ElfCodeMatchesData.f3LsSymAddrs f3LsSymAddrs_len_lt_2pow20]
      using h d hd
  rfl_kernel

private theorem f3LsMpl_rho_getD_eq {idx : Nat}
    (hlt : idx < ElfCodeMatchesData.lsInternedMultiLib.names.length) :
    ElfCodeMatchesPlaced.f3LsMpl.ρ (ElfCodeMatchesData.lsInternedMultiLib.names.getD idx "") =
      ElfCodeMatchesData.f3LsSymAddrs.getD idx 0#64 := by
  unfold ElfCodeMatchesPlaced.f3LsMpl ElfCodeMatchesData.f3LsMpl ElfCodeMatchesData.f3LsLayout
    Obj.Interned.MultiLayout.toMultiPlacement
  dsimp only [Obj.Interned.Layout.toPlacement, Obj.Interned.MultiLayout.dataLayout]
  rw [Obj.Interned.idxOf_getD ElfCodeMatchesData.ls_names_nodup hlt]

theorem cliElf_roLoaded_of_linkedAt {mpl : Obj.MultiPlacement}
    (hls : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {inputs : ProcessInputs} {s0 : State}
    (hload : cliElfImage.loadState inputs = .ok s0) :
    LibsignalRoLoaded mpl s0.mem := by
  obtain ⟨_, hp, hpl, hin⟩ := hls
  cases cliElf_parse.symm.trans hp
  have hρ_uniq := (ElfCodeMatchesPlaced.f3CliElf_libsignal_inElf_unique hpl hin).2.2.1
  have hne : 0 < libsignalSessionLib.blocks.length := by
    have h1 := Nat.beq_eq.mp ElfCodeMatchesData.libsignalBlocks_len
    have h2 := Nat.ble_eq.mp ElfCodeMatchesData.f3LsBlocksLen_ge_600
    omega
  have hpl0 := libsignalSessionLib.placeable_blockLib hne hpl
  have hids := ElfCodeMatchesData.ls_idsOk
  simp only [Obj.Interned.MultiLib.idsOk, Bool.and_eq_true, List.all_eq_true, Nat.blt_eq] at hids
  intro d hd hro
  have hd_int : d ∈ ElfCodeMatchesData.lsInternedMultiLib.toMultiPlacedLib.data := by
    rwa [← ElfCodeMatchesData.ls_toMultiPlacedLib_eq]
  rw [Obj.Interned.MultiLib.toMultiPlacedLib_data, List.mem_map] at hd_int
  obtain ⟨di, hdi, rfl⟩ := hd_int
  have hsym_lt : di.sym < ElfCodeMatchesData.lsInternedMultiLib.names.length := (hids.2 di hdi).1
  have hnone : Obj.lookupBlockSym (di.toInfo ElfCodeMatchesData.lsInternedMultiLib.names).sym
      libsignalSessionLib.blocks = none := (hpl.data_ok _ hd).1
  have hsym_mem : (di.toInfo ElfCodeMatchesData.lsInternedMultiLib.names).sym ∈
      ElfCodeMatchesData.lsInternedMultiLib.names := by
    dsimp only [Obj.Interned.Data.toInfo]
    rw [Obj.Interned.getD_of_lt hsym_lt]
    exact List.getElem_mem hsym_lt
  have hρ_eq : mpl.ρ (di.toInfo ElfCodeMatchesData.lsInternedMultiLib.names).sym =
      ElfCodeMatchesData.f3LsSymAddrs.getD di.sym 0#64 :=
    (hρ_uniq _ hsym_mem hnone).trans (f3LsMpl_rho_getD_eq hsym_lt)
  have hwin_d := List.all_eq_true.mp ls_rodata_in_window di hdi
  have hro_di : di.readOnly = true := hro
  simp only [hro_di, Bool.not_true, Bool.false_or, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hwin_d
  have hpd_eq := libsignalSessionLib.patchedData_blockLib hne hpl hd
  have hlen_pd : (libsignalSessionLib.patchedData mpl
      (di.toInfo ElfCodeMatchesData.lsInternedMultiLib.names)).length =
      di.bytes.length + di.zeroTail := by
    rw [← hpd_eq]
    exact PlacedLib.length_patchedData
      (lib := { (libsignalSessionLib.blockLib 0) with exports := [] })
      (pl := libsignalSessionLib.blockPlacement mpl 0)
      (fun r hr => (hpl0.data_relocs_ok _ hd r hr).2.1)
  have hem := hin.data _ hd
  intro k hk
  obtain ⟨p, hcell, _⟩ := hem k hk
  have hc := ElfImage.loadState_cell hload hcell
  have hk_lt : k < di.bytes.length + di.zeroTail := hlen_pd ▸ hk
  have ha_nat :
      (mpl.ρ (di.toInfo ElfCodeMatchesData.lsInternedMultiLib.names).sym + BitVec.ofNat 64 k).toNat =
        (ElfCodeMatchesData.f3LsSymAddrs.getD di.sym 0#64).toNat + k := by
    rw [hρ_eq, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega :
        (ElfCodeMatchesData.f3LsSymAddrs.getD di.sym 0#64).toNat + k < 2 ^ 64)]
  have hp_ro : p = Perm.ro :=
    cellAt_perm_ro_of_window (lo := f3LsRoLo) (hi := f3LsRoHi)
      ⟨by omega, by omega⟩ cliElf_segments_ro_window hcell
  rw [hp_ro, show Perm.ro.rwx = Perm.ro from rfl] at hc
  exact ⟨hc.1, hc.2, ElfImage.loadState_isLazyFree hload _⟩

theorem cliElf_frozen_of_linkedAt {mpl : Obj.MultiPlacement}
    (hls : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {inputs : ProcessInputs} {s0 : State}
    (hload : cliElfImage.loadState inputs = .ok s0) :
    LibsignalFrozen mpl s0.mem := by
  have ⟨_, hp, hpl, hin⟩ := hls
  cases cliElf_parse.symm.trans hp
  exact ⟨cliElf_roLoaded_of_linkedAt hls hload, MultiPlacedLib.codeLoaded_of_inElf hpl hin hload⟩

private theorem keepsFrozen_write8_of_perm_rw {m : Memory} {addr : BitVec 64} (val : BitVec 8)
    (hp : m.perm addr = some Perm.rw) : m.KeepsFrozen (m.write8 addr val) := by
  intro a ha
  have hne : a ≠ addr := by
    rintro rfl
    unfold Memory.Frozen at ha
    simp only [hp, Option.frozen, Perm.frozen] at ha
    exact Bool.noConfusion ha
  simp [Memory.write8, Memory.read8, Memory.perm, Memory.isLazyFree, Memory.isAnon, hne]

private theorem bv_add_1_1_tok (x : BitVec 64) : x + 1#64 + 1#64 = x + 2#64 := by
  rw [BitVec.add_assoc]; rfl

private theorem bv_add_2_1_tok (x : BitVec 64) : x + 2#64 + 1#64 = x + 3#64 := by
  rw [BitVec.add_assoc]; rfl

theorem keepsFrozen_cliTokenPatchPlacedAt {mpl : Obj.MultiPlacement} {elf : ElfImage}
    (hE : ElfStaticOk elf) (htok : CliElfTokenCellsPlacedAt mpl elf)
    {inputs : ProcessInputs} {s0 : State} (hload : elf.loadState inputs = .ok s0) :
    s0.mem.KeepsFrozen (cliTokenPatchPlaced mpl s0).mem := by
  have ps : s0.mem.perm (mpl.ρ tokenStorageName) = some .rw := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, show Perm.rw.rwx = Perm.rw from rfl] using
      ((htok.storage.holdsBytes hE.1 hE.2 hload) 0 (by decide)).2.1
  have p0 : s0.mem.perm (mpl.ρ tokenName + 8#64) = some .rw := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, show Perm.rw.rwx = Perm.rw from rfl] using
      ((htok.once.holdsBytes hE.1 hE.2 hload) 0 (by decide)).2.1
  have p1 : s0.mem.perm (mpl.ρ tokenName + 8#64 + 1#64) = some .rw :=
    ((htok.once.holdsBytes hE.1 hE.2 hload) 1 (by decide)).2.1
  have p2 : s0.mem.perm (mpl.ρ tokenName + 8#64 + 2#64) = some .rw :=
    ((htok.once.holdsBytes hE.1 hE.2 hload) 2 (by decide)).2.1
  have p3 : s0.mem.perm (mpl.ρ tokenName + 8#64 + 3#64) = some .rw :=
    ((htok.once.holdsBytes hE.1 hE.2 hload) 3 (by decide)).2.1
  have hmem : (cliTokenPatchPlaced mpl s0).mem =
      (((((s0.mem.write8 (mpl.ρ tokenStorageName) 0#8).write8
        (mpl.ρ tokenName + 8#64) 0#8).write8
        (mpl.ρ tokenName + 8#64 + 1#64) 0#8).write8
        (mpl.ρ tokenName + 8#64 + 2#64) 0#8).write8
        (mpl.ρ tokenName + 8#64 + 3#64) 0#8) := by
    simp only [cliTokenPatchPlaced, State.setMem, Memory.writeBytes,
      bv_add_1_1_tok, bv_add_2_1_tok]
  rw [hmem]
  exact ((((keepsFrozen_write8_of_perm_rw 0#8 ps).trans
    (keepsFrozen_write8_of_perm_rw 0#8 (by simpa only [Memory.perm_write8_apply] using p0))).trans
    (keepsFrozen_write8_of_perm_rw 0#8 (by simpa only [Memory.perm_write8_apply] using p1))).trans
    (keepsFrozen_write8_of_perm_rw 0#8 (by simpa only [Memory.perm_write8_apply] using p2))).trans
    (keepsFrozen_write8_of_perm_rw 0#8 (by simpa only [Memory.perm_write8_apply] using p3))

private def regionExecFrozenB (r : Snapshot.Region) : Bool :=
  !r.perm.x || (r.perm.r && !r.perm.w)

private theorem loadCellAt_execFrozen :
    ∀ (rs : List Snapshot.Region),
      rs.all regionExecFrozenB = true →
      MemExecFrozen ⟨Snapshot.loadCellAt rs⟩
  | [], _, a, hx => by
    simp [Memory.perm, Snapshot.loadCellAt] at hx
  | r :: tl, hall, a, hx => by
    simp only [List.all_cons, Bool.and_eq_true] at hall
    unfold Memory.perm Snapshot.loadCellAt at hx ⊢
    dsimp only [List.findSome?_cons] at hx ⊢
    by_cases hlt : (a - r.start).toNat < r.bytes.length
    · simp only [hlt, ↓reduceDIte, Option.x, Option.r, Option.w, Perm.rwx] at hx ⊢
      have hr := hall.1
      unfold regionExecFrozenB at hr
      simp only [hx, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at hr
      exact hr
    · simp only [hlt, ↓reduceDIte] at hx ⊢
      exact loadCellAt_execFrozen tl hall.2 a hx

private theorem mapZero_perm_f3 (m : Memory) (base : BitVec 64) (len : Nat) (a : BitVec 64) :
    (m.mapZero base len).perm a =
      if (a - base).toNat < len && !(m.perm a).mapped then some Perm.rw else m.perm a := by
  conv => lhs; unfold Memory.perm Memory.mapZero; dsimp only
  cases ((a - base).toNat < len && !(m.perm a).mapped) <;> rfl

private theorem mapZero_execFrozen {m : Memory} (hm : MemExecFrozen m)
    (base : BitVec 64) (len : Nat) :
    MemExecFrozen (m.mapZero base len) := by
  intro a hx
  rw [mapZero_perm_f3] at hx ⊢
  cases h : ((a - base).toNat < len && !(m.perm a).mapped)
  · simp only [h, Bool.false_eq_true, ↓reduceIte] at hx ⊢
    exact hm a hx
  · simp only [h, ↓reduceIte, Option.x, Perm.rw, Bool.false_eq_true] at hx

private theorem ite_error_ok {ε α : Type} {P : Prop} [Decidable P] {e : ε} {k : Except ε α} {v : α}
    (h : (if P then Except.error e else k) = Except.ok v) :
    k = Except.ok v := by
  by_cases hp : P
  · simp only [hp, ↓reduceIte] at h; nomatch h
  · simpa only [hp, ↓reduceIte] using h

private theorem buildInitialStack_perm_rw {img : ElfImage} {inputs : ProcessInputs}
    {sp : BitVec 64} {stackRegion : Snapshot.Region}
    (hb : buildInitialStack img inputs = .ok (sp, stackRegion)) :
    stackRegion.perm = Perm.rw := by
  unfold buildInitialStack at hb
  dsimp only [Bind.bind, Pure.pure, Except.bind, Except.pure] at hb
  replace hb := ite_error_ok hb
  replace hb := ite_error_ok hb
  replace hb := ite_error_ok hb
  replace hb := ite_error_ok hb
  replace hb := ite_error_ok hb
  replace hb := ite_error_ok hb
  replace hb := ite_error_ok hb
  replace hb := ite_error_ok hb
  replace hb := ite_error_ok hb
  injection hb with hpr
  exact (congrArg (Snapshot.Region.perm ∘ Prod.snd) hpr).symm

set_option maxRecDepth 4000000 in
private theorem f3PatchedElf_segments_execFrozen :
    f3PatchedElf.segments.all regionExecFrozenB = true := by
  rfl_kernel

private theorem elfLoadState_execFrozen {img : ElfImage}
    (hsegs : img.segments.all regionExecFrozenB = true)
    {inputs : ProcessInputs} {s0 : State}
    (hload : img.loadState inputs = .ok s0) :
    MemExecFrozen s0.mem := by
  unfold ElfImage.loadState at hload
  dsimp only [Bind.bind, Pure.pure, Except.bind, Except.pure] at hload
  split at hload; · contradiction
  split at hload; · contradiction
  split at hload; · contradiction
  generalize hbis : buildInitialStack img inputs = r at hload
  cases r with
  | error _ => contradiction
  | ok pr =>
    obtain ⟨sp, stackRegion⟩ := pr
    dsimp only at hload
    injection hload with hs0
    rw [← hs0]
    dsimp only
    apply mapZero_execFrozen
    apply loadCellAt_execFrozen
    rw [List.all_append, Bool.and_eq_true]
    refine ⟨hsegs, ?_⟩
    simp [regionExecFrozenB, buildInitialStack_perm_rw hbis, Perm.rw]

/-- Every initial state `s0` loaded from `patchElfTokensPlacedAt mpl cliElfImage` satisfies
`F3CodeOk mpl mmpl s0.mem`. -/
theorem f3CodeOk_of_patchedLoadState {mpl mmpl : Obj.MultiPlacement}
    (hls : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hmng : VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl)
    {inputs : ProcessInputs} {s0 : State}
    (hload : (patchElfTokensPlacedAt mpl cliElfImage).loadState inputs = .ok s0) :
    F3CodeOk mpl mmpl s0.mem := by
  have htok := cliElf_tokenCellsPlacedAt_of_linkedAt hls
  have hmap := loadState_patchElfTokensPlacedAt cliElf_staticOk htok inputs
  have hload_map := hload
  rw [hmap] at hload_map
  cases hraw : cliElfImage.loadState inputs with
  | error _ =>
    rw [hraw] at hload_map
    cases hload_map
  | ok sRaw =>
    rw [hraw] at hload_map
    simp only [Except.map, Except.ok.injEq] at hload_map
    have hkf : sRaw.mem.KeepsFrozen s0.mem := by
      rw [← hload_map]
      exact keepsFrozen_cliTokenPatchPlacedAt cliElf_staticOk htok hraw
    have hlsRo0 : LibsignalCodeRoLoaded mpl sRaw.mem :=
      CryptoVerification.LibsignalTripleRatchet.Record.LibsignalCodeRoLoaded.of_libsignalFrozen
        (cliElf_frozen_of_linkedAt hls hraw)
    obtain ⟨_, hp_mng, hpl_mng, hin_mng⟩ := hmng
    cases cliElf_parse.symm.trans hp_mng
    have hmngCode0 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl sRaw.mem :=
      MultiPlacedLib.codeLoaded_of_inElf hpl_mng hin_mng hraw
    have hload_canon : f3PatchedElf.loadState inputs = .ok s0 :=
      f3PatchedElf_eq_of_linkedAt hls ▸ hload
    have hrxCode : Tie.f3TrialRxProg.CodeLoaded s0.mem :=
      f3PatchedElf_rxProgram_eq ▸ f3MatchesImage_codeLoaded f3PatchedElf_matchesImage hload_canon
    have hexecFrz : MemExecFrozen s0.mem :=
      elfLoadState_execFrozen f3PatchedElf_segments_execFrozen hload_canon
    exact ⟨{ lsRo := hlsRo0.of_keepsFrozen hkf
             mngCode := hmngCode0.of_keepsFrozen hkf
             rxCode := hrxCode
             fromLoad := ⟨inputs, s0, hload, Memory.KeepsFrozen.refl s0.mem⟩ },
           hexecFrz⟩

/-! ## `cliStaticsPlacedAt` Framing Across Startup and Exit -/

private noncomputable def f3CliStaticsAtoms : List RwAtom :=
  [ .u64 (ElfCodeMatchesPlaced.f3LsMpl.ρ coinsNextSym) 1#64,
    .u64 (ElfCodeMatchesPlaced.f3LsMpl.ρ coinsLeftSym) 0#64,
    .u8  (ElfCodeMatchesPlaced.f3LsMpl.ρ tokenStorageName) 0#8,
    .u32 (ElfCodeMatchesPlaced.f3LsMpl.ρ tokenName + 8#64) 0#32,
    .u64 (ElfCodeMatchesPlaced.f3LsMpl.ρ lsLogFilterSym) 0#64 ]

set_option maxRecDepth 4000000 in
private theorem f3PatchedElf_statics_seg3_chk :
    ∃ seg3 : Snapshot.Region,
      f3PatchedElf.segments[3]? = some seg3 ∧
      seg3.perm = Perm.rw ∧
      (f3CliStaticsAtoms.all fun x =>
        checkSegSlice seg3 seg3.bytes.length x.addr x.rawBytes &&
          decide (x.addr.toNat + x.rawBytes.length ≤ f3StdLayout.brkStart.toNat)) = true ∧
      intervalsPairwiseDisjoint
        ((f3CliStaticsAtoms ++ f3AllRwAtoms f3StdLayout).map fun x =>
          (x.addr.toNat, x.rawBytes.length)) = true := by
  refine ⟨f3PatchedElf.segments[3]'(by simp [f3PatchedElf, patchElfTokensPlacedAt,
      patchElfByte, cliElf_seg3_lt]),
    by simp, by rfl_kernel, by rfl_kernel, by rfl_kernel⟩

private theorem cliStaticsPlacedAt_eq_f3LsMpl_of_linkedAt {mpl : Obj.MultiPlacement}
    (hls : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    cliStaticsPlacedAt mpl =
      cliStaticsPlacedAt ElfCodeMatchesPlaced.f3LsMpl := by
  have hst := ElfCodeMatchesPlaced.f3CliElf_statics_rho_eq_of_linkedAt hls
  unfold cliStaticsPlacedAt coinsStaticsPlacedAt tokenInitPlacedAtMpl lsLogOffAt
  rw [hst.1, hst.2.1, hst.2.2.1, hst.2.2.2.1, hst.2.2.2.2]

private theorem rwAtomListSep_f3CliStaticsAtoms_entails :
    rwAtomListSep f3CliStaticsAtoms ⊢
      cliStaticsPlacedAt ElfCodeMatchesPlaced.f3LsMpl := by
  dsimp only [f3CliStaticsAtoms, rwAtomListSep, RwAtom.toSepProp,
    cliStaticsPlacedAt, coinsStaticsPlacedAt, tokenInitPlacedAtMpl, lsLogOffAt]
  have h1 : (ElfCodeMatchesPlaced.f3LsMpl.ρ coinsNextSym ↦₆₄ 1#64) ⊢
      (∃∗ v : BitVec 64, ElfCodeMatchesPlaced.f3LsMpl.ρ coinsNextSym ↦₆₄ v) :=
    Entails.sepExists_right 1#64 (Entails.refl _)
  have h2 : (ElfCodeMatchesPlaced.f3LsMpl.ρ coinsLeftSym ↦₆₄ 0#64) ⊢
      (∃∗ v : BitVec 64, ElfCodeMatchesPlaced.f3LsMpl.ρ coinsLeftSym ↦₆₄ v) :=
    Entails.sepExists_right 0#64 (Entails.refl _)
  refine Entails.trans (sepConj_mono h1 (sepConj_mono_left h2)) ?_
  sep_entail

private theorem f3PatchedElf_supportedOn_statics_and_initGlobals {inputs : ProcessInputs} {s0 : State}
    (hload : f3PatchedElf.loadState inputs = .ok s0) :
    SupportedOn 0#64 (fun k => 0 ≤ k ∧ k < f3StdLayout.brkStart.toNat) s0.mem
      (rwAtomListSep f3CliStaticsAtoms ∗ (F3InitGlobals f3StdLayout ∗ StdExtraRw f3StdLayout)) := by
  obtain ⟨hwf, _, _, _, hbrk_eq, _, _, _, _, _, rwSeg, _, _, _, hrw, _, _, _, _, _, _, hrwC⟩ :=
    f3MatchesImage_segments f3PatchedElf_matchesImage
  obtain ⟨seg3, hseg3, hperm3, hall, hdisj⟩ := f3PatchedElf_statics_seg3_chk
  have hbel_all : f3PatchedElf.segments.all (Snapshot.Below f3StdLayout.brkStart) = true := by
    have hwf' := hwf; unfold ElfImage.WellFormed at hwf'
    simp only [Bool.and_eq_true] at hwf'; rw [← hbrk_eq]; exact hwf'.2
  have hbel := List.all_eq_true.mp hbel_all rwSeg (List.mem_of_getElem? hrw)
  simp only [Snapshot.Below, decide_eq_true_eq] at hbel
  unfold f3CheckRwSegment at hrwC; simp only [Bool.and_eq_true, beq_iff_eq] at hrwC
  have hs := supportedOn_rwAtomList (f3CliStaticsAtoms ++ f3AllRwAtoms f3StdLayout) (fun x hx => by
    rcases List.mem_append.mp hx with hxS | hxG
    · have hxC := List.all_eq_true.mp hall x hxS
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hxC
      have ⟨hhb, _, hhi⟩ := holdsBytes_of_checkSegSlice hwf hload hseg3 hxC.1
      rw [hperm3] at hhb
      exact ⟨by omega, hhb⟩
    · have hxC := List.all_eq_true.mp hrwC.1.1.2 x hxG; simp only [Bool.and_eq_true] at hxC
      have ⟨hhb, _, hhi⟩ := holdsBytes_of_checkSegSlice hwf hload hrw hxC.2
      rw [hrwC.1.1.1.1.1.1.1.1.1.1.1.1] at hhb; exact ⟨by omega, hhb⟩) hdisj
  have hsep_eq : rwAtomListSep (f3CliStaticsAtoms ++ f3AllRwAtoms f3StdLayout) =
      rwAtomListSep f3CliStaticsAtoms ∗ (F3InitGlobals f3StdLayout ∗ StdExtraRw f3StdLayout) := by
    rw [rwAtomListSep_append, f3AllRwAtoms_sep_eq f3StdLayout]
  refine (SupportedOn.congr_prop hsep_eq hs).widen fun k ⟨x, hx, hk1, hk2⟩ => ?_
  rcases List.mem_append.mp hx with hxS | hxG
  · have hxC := List.all_eq_true.mp hall x hxS
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hxC
    omega
  · have hxC := List.all_eq_true.mp hrwC.1.1.2 x hxG; simp only [Bool.and_eq_true] at hxC
    have hb := hxC.2; unfold checkSegSlice at hb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    omega

private def f3EmptyFsInputs (i : Inputs) : ProcessInputs :=
  { cliInputs i with stdin := [], files := [], dirs := [] }

private theorem bytesOfString_length (s : String) : (bytesOfString s).length = s.length := by
  simp [bytesOfString, String.length_toList]

private theorem zero_not_mem_bytesOfString {s : String}
    (h : ∀ c ∈ s.toList, 0 < c.toNat ∧ c.toNat < 128) :
    0#8 ∉ bytesOfString s := by
  intro hm
  simp only [bytesOfString, List.mem_map] at hm
  obtain ⟨c, hc, h0⟩ := hm
  have ⟨hpos, hlt⟩ := h c hc
  have htn := congrArg BitVec.toNat h0
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : c.toNat < 256)] at htn
  omega

private theorem foldl_argv_len_le_sum (xs : List String) (acc : Nat) :
    (xs.map bytesOfString).foldl (fun n s => n + (s.length + 1)) acc + 8 * xs.length =
      acc + (xs.map fun a => a.length + 1 + 8).sum := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.foldl_cons, List.length_cons, List.sum_cons,
      bytesOfString_length]
    have := ih (acc + (x.length + 1))
    omega

private theorem le_sum_of_mem_nat {x : Nat} {xs : List Nat} (h : x ∈ xs) : x ≤ xs.sum := by
  induction xs with
  | nil => cases h
  | cons y ys ih =>
    rcases List.mem_cons.mp h with rfl | hm
    · simp only [List.sum_cons]; omega
    · simp only [List.sum_cons]; have := ih hm; omega

private theorem argv_elem_len_le {a : String} {argv : List String}
    (hmem : a ∈ argv) (hfit : CryptoVerification.SignalSession.ArgvFitsInitialStack argv) :
    a.length + 1 + 8 ≤ 16384 := by
  unfold CryptoVerification.SignalSession.ArgvFitsInitialStack at hfit
  have hle : a.length + 1 + 8 ≤ (argv.map fun x => x.length + 1 + 8).sum :=
    le_sum_of_mem_nat (List.mem_map_of_mem hmem)
  omega

private theorem f3EmptyFsInputs_valid {i : Inputs} (hi : CliInputsOk i) :
    (f3EmptyFsInputs i).Valid := by
  obtain ⟨hprint, hfit⟩ := hi
  have hinit : (f3EmptyFsInputs i).init.Valid :=
    show ({ stackSize := 8388608 } : ProcessInit).Valid from
      (ProcessInit.check_iff_valid _).mp (by decide)
  have hfs : FsValid (f3EmptyFsInputs i) :=
    (FsValid.check_iff (f3EmptyFsInputs i)).mp rfl
  have hargs : ArgsValid (f3EmptyFsInputs i) := by
    refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · simp [f3EmptyFsInputs, cliInputs, processInputs]
    · intro s hs
      simp only [f3EmptyFsInputs, cliInputs, processInputs,
        List.map_cons, List.mem_cons, List.mem_map] at hs
      rcases hs with rfl | hmem
      · exact of_decide_eq_true (by decide)
      · obtain ⟨a, ⟨ha, rfl⟩⟩ := hmem
        exact zero_not_mem_bytesOfString (hprint a ha).2
    · intro s hs
      simp [f3EmptyFsInputs, cliInputs, processInputs] at hs
    · simp [f3EmptyFsInputs, cliInputs, processInputs]
    · intro s hs
      simp only [f3EmptyFsInputs, cliInputs, processInputs, List.append_nil,
        List.map_cons, List.mem_cons, List.mem_map] at hs
      rcases hs with rfl | hmem
      · exact of_decide_eq_true (by decide)
      · obtain ⟨a, ⟨ha, rfl⟩⟩ := hmem
        rw [bytesOfString_length]
        have := argv_elem_len_le ha hfit
        unfold MAX_ARG_STRLEN Obj.pageSize; omega
    · simp only [f3EmptyFsInputs, cliInputs, processInputs]
      decide
    · unfold argBytes argLimit STK_LIM ARG_MAX
      simp only [f3EmptyFsInputs, cliInputs, processInputs, List.map_cons,
        List.foldl_cons, List.foldl_nil, List.length_cons, List.length_nil]
      have hbin : (bytesOfString "libsignal-cli").length = 13 := by decide
      rw [hbin]
      have hfold := foldl_argv_len_le_sum i.argv (0 + (13 + 1))
      unfold CryptoVerification.SignalSession.ArgvFitsInitialStack at hfit
      have hlen_map : (List.map bytesOfString i.argv).length = i.argv.length := List.length_map _
      rw [hlen_map]
      omega
  exact ⟨hargs, hinit, hfs⟩

private theorem loadState_f3CliInputs_of_empty {elf : ElfImage} {i : Inputs} {s0_0 : State}
    (hl : InputsLoadable i)
    (hload0 : elf.loadState (f3EmptyFsInputs i) = .ok s0_0) :
    ∃ s0 : State,
      elf.loadState (cliInputs i) = .ok s0 ∧
      s0_0 = s0.setFs (initFsState (f3EmptyFsInputs i)) ∧
      s0.fs = initFsState (cliInputs i) ∧
      s0.trace = [] ∧
      s0.mem = s0_0.mem ∧
      s0.brk = s0_0.brk ∧
      s0.brkStart = s0_0.brkStart ∧
      s0.physMemAvail = s0_0.physMemAvail := by
  have hd_any : (cliInputs i).dirs.any (fun d => hasLeadingSlash d || hasDotDot d) = false := by
    rw [List.any_eq_false]
    intro d hd
    have ⟨h1, h2⟩ := hl.1 d hd
    simp [h1, h2]
  have hf_any : (cliInputs i).files.any (fun (p, bs) =>
      hasLeadingSlash p || hasDotDot p || !decide (bs.length ≤ MAX_LFS_FILESIZE)) = false := by
    rw [List.any_eq_false]
    rintro ⟨p, bs⟩ hp
    have ⟨⟨h1, h2⟩, h3⟩ := hl.2 (p, bs) hp
    simp [h1, h2, h3]
  have hb_eq : buildInitialStack elf (cliInputs i) = buildInitialStack elf (f3EmptyFsInputs i) := rfl
  dsimp only [ElfImage.loadState, Bind.bind, Pure.pure, Except.bind, Except.pure] at hload0 ⊢
  have hd0 : (f3EmptyFsInputs i).dirs.any (fun d => hasLeadingSlash d || hasDotDot d) = false := rfl
  have hf0 : (f3EmptyFsInputs i).files.any (fun (p, bs) =>
      hasLeadingSlash p || hasDotDot p || !decide (bs.length ≤ MAX_LFS_FILESIZE)) = false := rfl
  rw [hd0, hf0] at hload0
  rw [hd_any, hf_any, hb_eq]
  cases hwf : (!elf.WellFormed) <;> simp only [hwf, Bool.false_eq_true, ↓reduceIte] at hload0 ⊢
  · generalize hbis : buildInitialStack elf (f3EmptyFsInputs i) = r at hload0 ⊢
    cases r with
    | error _ => contradiction
    | ok pr =>
      obtain ⟨sp, stackRegion⟩ := pr
      dsimp only at hload0 ⊢
      cases hload0
      exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · contradiction

private theorem rwAtomListSep_f3BssAtoms (L : StdBinaryLayout) :
    F3BssGlobals L =
      (L.threadListLockAddr ↦₃₂ 0#32) ∗ (L.sysinfoAddr ↦₆₄ 0#64) ∗ (L.hwcapAddr ↦₆₄ 0#64) ∗
      (L.finalizedAddr ↦₈ 0#8) ∗ (L.initializedAddr ↦₈ 0#8) ∗
      (L.stdDetectCacheAddr ↦₆₄ 0#64) ∗ (L.environAddr ↦₆₄ 0#64) ∗
      (L.prognameAddr ↦₆₄ 0#64) ∗ (L.prognameFullAddr ↦₆₄ 0#64) ∗
      (L.haveLseAtomicsAddr ↦₈ 0#8) ∗ (L.stdinUsedAddr ↦₆₄ 0#64) ∗
      (if L.stdoutUsedAddr == L.stdinUsedAddr then emp else L.stdoutUsedAddr ↦₆₄ 0#64) ∗
      (L.oflHeadAddr ↦₆₄ 0#64) ∗ (L.oflLockAddr ↦₃₂ 0#32) := by
  unfold F3BssGlobals f3BssAtoms
  cases (L.stdoutUsedAddr == L.stdinUsedAddr) with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte,
      List.nil_append, List.cons_append, rwAtomListSep, RwAtom.toSepProp]
  | true =>
    simp only [↓reduceIte,
      List.nil_append, List.cons_append, rwAtomListSep, RwAtom.toSepProp]
    sep_ac_rfl

private def f3PreTlsSep (L : StdBinaryLayout) (sp0 : BitVec 64) : SepProp :=
  memRegion (sp0 - 544#64) 96 ∗ (L.phdrAddr ↦ᵣ L.phdrBytes) ∗
    (L.defaultStacksizeAddr ↦₃₂ 131072#32) ∗ StdTlsGlobals L ∗
    (L.libcAddr ↦₈ 0#8) ∗ StdLibcTlsZero L

private def f3PostTlsSep (L : StdBinaryLayout) (sp0 sysinfoVal : BitVec 64) : SepProp :=
  ((L.builtinTlsAddr + 200#64 - 164#64) ↦₃₂ 0#32) ∗ (L.libcAddr ↦₈ 1#8) ∗
    memRegion (sp0 - 544#64) 96 ∗ (L.phdrAddr ↦ᵣ L.phdrBytes) ∗
    (L.defaultStacksizeAddr ↦₃₂ 131072#32) ∗ F3TlsState L sysinfoVal

private def f3InitAllSep (L : StdBinaryLayout) (img : ElfImage) (inputs : ProcessInputs) : SepProp :=
  let sl := StackLayout.of img inputs
  F3RoConstants L ∗ StdExtraRo L ∗ F3InitGlobals L ∗ StdExtraRw L ∗
    memRegion (sl.sp0 - 8371824#64) 8371824 ∗
    (sl.sp0 ↦₆₄ᵣ BitVec.ofNat 64 inputs.argv.length) ∗
    (sl.argvTableAddr ↦₆₄ᵣ* (sl.argvAddrs ++ [0#64])) ∗
    (sl.envpTableAddr ↦₆₄ᵣ* (sl.envpAddrs ++ [0#64])) ∗
    (sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗
    (sl.randomAddr ↦ₛ inputs.init.auxv.randomBytes) ∗
    (sl.platformAddr ↦ᵣ platformCStringBytes) ∗
    (sl.argvBase ↦ᵣ sl.upperStrBytes)

private theorem scratch_supportedOn_of_headroom {img : ElfImage} {inputs : ProcessInputs}
    {s0 : State} (h : InitialStackInfo img inputs s0) {K : Nat}
    (hK : inputs.init.stackTop.toNat - inputs.init.stackSize + K ≤
      (StackLayout.of img inputs).sp0.toNat) :
    let L := StackLayout.of img inputs
    SupportedOn 0#64 (fun k => L.sp0.toNat - K ≤ k ∧ k < L.sp0.toNat) s0.mem
      (memRegion (L.sp0 - BitVec.ofNat 64 K) K) := by
  have hperm := h.s0_perm_rw_below_sp0
  have hnolf := h.s0_isLazyFree
  clear h; dsimp only
  generalize hsp : (StackLayout.of img inputs).sp0 = sp0 at *; clear hsp
  have hlt := sp0.isLt
  have hbase : (sp0 - BitVec.ofNat 64 K).toNat = sp0.toNat - K := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hsup := SupportedOn.of_memRegion_rw0 (addr := sp0 - BitVec.ofNat 64 K) (len := K)
    (m := s0.mem) (by rw [hbase]; omega)
    (fun a ha => by
      unfold InRegion at ha; have := a.isLt
      rw [BitVec.toNat_sub, hbase] at ha
      exact hperm a (by omega) (by omega))
    (fun a _ => hnolf a)
  rwa [hbase, show sp0.toNat - K + K = sp0.toNat by omega] at hsup

private theorem s0_satisfies_f3InitAllSep_and_statics {mpl : Obj.MultiPlacement}
    (hls : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {inputs : ProcessInputs} {s0 : State}
    (hload : f3PatchedElf.loadState inputs = .ok s0)
    (hinfo : InitialStackInfo f3PatchedElf inputs s0) (hvalid : inputs.Valid)
    (hhr8 : inputs.init.stackTop.toNat - inputs.init.stackSize + 8371824 ≤
      (StackLayout.of f3PatchedElf inputs).sp0.toNat) :
    s0.mem ⊨ f3InitAllSep f3StdLayout f3PatchedElf inputs ∗
      cliStaticsPlacedAt mpl := by
  have hseg := f3MatchesImage_segments f3PatchedElf_matchesImage
  have hbrk_eq := hseg.2.2.2.2.1
  have hbrk_le := hseg.2.2.2.2.2.1.2
  have hfl := hinfo.stackBase_floor
  unfold STACK_BASE_MIN at hfl
  have htop_pos : (StackLayout.of f3PatchedElf inputs).sp0.toNat ≤ inputs.init.stackTop.toNat := by
    have := hinfo.addrs_nat; omega
  have h01 := SupportedOn.bupd_intro (f3PatchedElf_supportedOn_statics_and_initGlobals hload)
  have h2_sc := SupportedOn.bupd_intro (scratch_supportedOn_of_headroom hinfo hhr8)
  have h2_0 := hinfo.stack_supportedOn_bupd hvalid.auxv.random16 (K := 0) (Nat.zero_le _)
  have h2 := SupportedOn.sepConj_bupd_interval
    (lo := (StackLayout.of f3PatchedElf inputs).sp0.toNat - 8371824)
    (hi := inputs.init.stackTop.toNat) h2_sc h2_0 (by omega) (by omega) (by omega)
  have h012 := SupportedOn.sepConj_bupd_interval
    (lo := 0) (hi := inputs.init.stackTop.toNat) h01 h2 (by omega) (by omega) (by omega)
  have hsat := f3MatchesImage_satisfies_roConstants f3PatchedElf_matchesImage hload
    (SupportedOn.satisfies_bupd h012)
  have hmr0 : memRegion ((StackLayout.of f3PatchedElf inputs).sp0 - 8371824#64) 8371824 ∗
      memRegion ((StackLayout.of f3PatchedElf inputs).sp0 - 0#64) 0 =
      memRegion ((StackLayout.of f3PatchedElf inputs).sp0 - 8371824#64) 8371824 := by
    have hs := memRegion_split_le ((StackLayout.of f3PatchedElf inputs).sp0 - 8371824#64)
      8371824 8371824 (by decide) (by decide)
    rw [show (StackLayout.of f3PatchedElf inputs).sp0 - 8371824#64 + BitVec.ofNat 64 8371824 =
      (StackLayout.of f3PatchedElf inputs).sp0 - 0#64 by bv_lin] at hs
    exact hs.symm
  rw [cliStaticsPlacedAt_eq_f3LsMpl_of_linkedAt hls]
  refine Satisfies.mono ?_ hsat
  dsimp only [f3InitAllSep]
  rw [← sepConj_assoc (memRegion ((StackLayout.of f3PatchedElf inputs).sp0 - 8371824#64) 8371824)
    (memRegion ((StackLayout.of f3PatchedElf inputs).sp0 - 0#64) 0), hmr0]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
      (sepConj_mono_left rwAtomListSep_f3CliStaticsAtoms_entails)))) ?_
  sep_entail

private theorem absorb_ro_pad {U C Pad : SepProp}
    (hdup : (U ∗ (C ∗ Pad)) = U) (hc : (C ∗ C) = C) :
    U ⊢ C ∗ U := by
  refine Entails.trans (Entails.of_eq hdup.symm) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left (Entails.of_eq hc.symm))) ?_
  refine Entails.trans (Q := C ∗ (U ∗ (C ∗ Pad))) (by sep_entail) ?_
  exact sepConj_mono_right (Entails.of_eq hdup)

private theorem argvTable_dup_argvAtRO {img : ElfImage} {inputs : ProcessInputs} {s0 : State}
    (hinfo : InitialStackInfo img inputs s0) (hargs : ArgsValid inputs) :
    let sl := StackLayout.of img inputs
    ((sl.argvTableAddr ↦₆₄ᵣ* (sl.argvAddrs ++ [0#64])) ∗ (sl.argvBase ↦ᵣ sl.upperStrBytes)) ⊢
      argvAtRO sl.argvTableAddr inputs.argv ∗
        (sl.argvTableAddr ↦₆₄ᵣ* (sl.argvAddrs ++ [0#64])) ∗
        (sl.argvBase ↦ᵣ sl.upperStrBytes) := by
  dsimp only
  let sl := StackLayout.of img inputs
  have hlen : sl.argvAddrs.length = inputs.argv.length := hinfo.argvAddrs_length
  suffices hgen : ∀ (k : Nat), k ≤ inputs.argv.length →
      (((sl.argvTableAddr + BitVec.ofNat 64 (8 * k)) ↦₆₄ᵣ* (sl.argvAddrs.drop k ++ [0#64])) ∗
        (sl.argvBase ↦ᵣ sl.upperStrBytes)) ⊢
      argvAtRO (sl.argvTableAddr + BitVec.ofNat 64 (8 * k)) (inputs.argv.drop k) ∗
        ((sl.argvTableAddr + BitVec.ofNat 64 (8 * k)) ↦₆₄ᵣ* (sl.argvAddrs.drop k ++ [0#64])) ∗
        (sl.argvBase ↦ᵣ sl.upperStrBytes) by
    simpa only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, List.drop_zero] using
      hgen 0 (Nat.zero_le _)
  intro k hk
  induction hd : inputs.argv.length - k generalizing k with
  | zero =>
    have hk_eq : k = inputs.argv.length := by omega
    subst hk_eq
    have hd1 : sl.argvAddrs.drop inputs.argv.length = [] := List.drop_eq_nil_of_le (by omega)
    rw [hd1, List.drop_length, List.nil_append]
    simp only [argvAtRO, pointsToWords64RO_cons, pointsToWords64RO_nil, sepConj_emp]
    refine Entails.trans (sepConj_mono_left (Entails.of_eq (pointsTo64RO_dup _ _).symm)) (by sep_entail)
  | succ rem ih =>
    have hk_lt : k < inputs.argv.length := by omega
    have hk_lt' : k < sl.argvAddrs.length := by omega
    have hd_a : sl.argvAddrs.drop k = sl.argvAddrs[k] :: sl.argvAddrs.drop (k + 1) :=
      List.drop_eq_getElem_cons hk_lt'
    have hd_v : inputs.argv.drop k = inputs.argv[k] :: inputs.argv.drop (k + 1) :=
      List.drop_eq_getElem_cons hk_lt
    rw [hd_a, hd_v, List.cons_append]
    simp only [argvAtRO, pointsToWords64RO_cons]
    have hstep_addr : (sl.argvTableAddr + BitVec.ofNat 64 (8 * k)) + 8#64 =
        sl.argvTableAddr + BitVec.ofNat 64 (8 * (k + 1)) := by
      rw [BitVec.add_assoc, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add]
      exact congrArg (sl.argvTableAddr + BitVec.ofNat 64 ·) (by omega)
    rw [hstep_addr]
    obtain ⟨pad, _, _, _, _, hdup_str⟩ := hinfo.dup_argv_cstr_padded hargs hk_lt
    have habs_str : (sl.argvBase ↦ᵣ sl.upperStrBytes) ⊢
        (sl.argvAddrs[k] ↦ᵣ (inputs.argv[k] ++ [0#8])) ∗ (sl.argvBase ↦ᵣ sl.upperStrBytes) := by
      have hdup_str' : ((sl.argvBase ↦ᵣ sl.upperStrBytes) ∗
          ((sl.argvAddrs[k] ↦ᵣ (inputs.argv[k] ++ [0#8])) ∗
            ((sl.argvAddrs[k] + BitVec.ofNat 64 (inputs.argv[k] ++ [0#8]).length) ↦ᵣ pad))) =
          (sl.argvBase ↦ᵣ sl.upperStrBytes) := by
        dsimp only [sl]; rw [← pointsToBytesRO_append]; exact hdup_str
      exact absorb_ro_pad hdup_str' (pointsToBytesRO_dup _ _)
    have hih := ih (k + 1) (by omega) (by omega)
    refine Entails.trans ?_
      (sepConj_mono_left (Entails.sepExists_right sl.argvAddrs[k] (Entails.refl _)))
    dsimp only [cStrAtRO]
    refine Entails.trans
      (sepConj_mono_left (sepConj_mono_left (Entails.of_eq (pointsTo64RO_dup _ _).symm))) ?_
    refine Entails.trans
      (Q := ((sl.argvTableAddr + BitVec.ofNat 64 (8 * k)) ↦₆₄ᵣ sl.argvAddrs[k]) ∗
        ((sl.argvTableAddr + BitVec.ofNat 64 (8 * k)) ↦₆₄ᵣ sl.argvAddrs[k]) ∗
        (((sl.argvTableAddr + BitVec.ofNat 64 (8 * (k + 1))) ↦₆₄ᵣ*
          (sl.argvAddrs.drop (k + 1) ++ [0#64])) ∗
          ((sl.argvAddrs[k] ↦ᵣ (inputs.argv[k] ++ [0#8])) ∗
            (sl.argvBase ↦ᵣ sl.upperStrBytes))))
      (Entails.trans (by sep_entail)
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          habs_str))))
      ?_
    refine Entails.trans
      (Q := ((sl.argvTableAddr + BitVec.ofNat 64 (8 * k)) ↦₆₄ᵣ sl.argvAddrs[k]) ∗
        (sl.argvAddrs[k] ↦ᵣ (inputs.argv[k] ++ [0#8])) ∗
        ((sl.argvTableAddr + BitVec.ofNat 64 (8 * k)) ↦₆₄ᵣ sl.argvAddrs[k]) ∗
        (((sl.argvTableAddr + BitVec.ofNat 64 (8 * (k + 1))) ↦₆₄ᵣ*
          (sl.argvAddrs.drop (k + 1) ++ [0#64])) ∗
          (sl.argvBase ↦ᵣ sl.upperStrBytes)))
      (by sep_entail)
      ?_
    exact Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hih)))
      (by sep_entail)

private theorem pointsToBytes_flatMap_u64 {a : BitVec 64} (ws : List (BitVec 64))
    (hal : a.toNat % 8 = 0) (hbnd : a.toNat + 8 * ws.length ≤ 2 ^ 48) :
    (a ↦ₛ (ws.flatMap fun w => List.ofFn (fun i : Fin 8 => w.extractLsb' (8 * i.val) 8))) ⊢
      (a ↦₆₄* ws) := by
  induction ws generalizing a with
  | nil =>
    simp only [List.flatMap_nil, pointsToBytes_nil, pointsToWords64_nil]
    exact Entails.refl _
  | cons w ws ih =>
    simp only [List.flatMap_cons, List.length_cons] at hbnd ⊢
    have hlen8 : (List.ofFn (fun i : Fin 8 => w.extractLsb' (8 * i.val) 8)).length = 8 := by simp
    rw [pointsToBytes_append a (List.ofFn (fun i : Fin 8 => w.extractLsb' (8 * i.val) 8)) _, hlen8]
    have ha8_nat : (a + 8#64).toNat = a.toNat + 8 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
    have hw : (a ↦ₛ List.ofFn (fun i : Fin 8 => w.extractLsb' (8 * i.val) 8)) ⊢ (a ↦₆₄ w) := by
      rw [pointsTo64_eq_pointsToBytes]
      exact Entails.refl _
    rw [pointsToWords64_cons]
    exact sepConj_mono hw (ih (by omega) (by omega))

private theorem auxv_entails_mallocngAuxvAt {img : ElfImage} {inputs : ProcessInputs} {s0 : State}
    (hinfo : InitialStackInfo img inputs s0) (hvalid : inputs.Valid) :
    let sl := StackLayout.of img inputs
    ((sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗
      (sl.randomAddr ↦ₛ inputs.init.auxv.randomBytes)) ⊢
      MallocngAuxvAt sl.auxvTableAddr ∗
        (sl.randomAddr ↦ₛ inputs.init.auxv.randomBytes.take 8) := by
  dsimp only
  have hrand16 := hvalid.auxv.random16
  have han := hinfo.addrs_nat; dsimp only at han
  obtain ⟨_, _, haux_nat, haux_le, hplat_nat, hargvB_nat, _, _, hupper_top⟩ := han
  have htop48 : inputs.init.stackTop.toNat ≤ 2 ^ 48 := hinfo.stackTop_align.2.2
  have hsp16 := hinfo.sp0_align16
  obtain ⟨prePairs, sufPairs, hsplit_eq, _, hps_le, hpre_no, hsuf_no⟩ :=
    mkAuxvEntries_split_random img hvalid.auxv
      (StackLayout.of img inputs).platformAddr
      (StackLayout.of img inputs).randomAddr
      (StackLayout.of img inputs).execfnAddr
  have hauxE_split : (StackLayout.of img inputs).auxvEntries =
      prePairs ++ [(AuxvTag.random, (StackLayout.of img inputs).randomAddr)] ++ sufPairs :=
    hinfo.auxvEntries_eq.trans hsplit_eq
  have hauxE_len : (StackLayout.of img inputs).auxvEntries.length =
      prePairs.length + sufPairs.length + 1 := by
    rw [hauxE_split]; simp; omega
  rw [hauxE_len] at haux_le
  let ws := ((prePairs ++ [(25#64, (StackLayout.of img inputs).randomAddr)] ++
    sufPairs ++ [(0#64, 0#64)]).flatMap fun (t, v) => [t, v])
  have hws_len : ws.length = 2 * (prePairs.length + sufPairs.length + 2) := by
    have hfl : ∀ xs : List (BitVec 64 × BitVec 64),
        (xs.flatMap fun (t, v) => [t, v]).length = 2 * xs.length := by
      intro xs; induction xs with
      | nil => simp
      | cons _ tl ih => simp [ih]; omega
    rw [hfl]; simp; omega
  have henc_eq : encodeAuxvBytes (StackLayout.of img inputs).auxvEntries =
      ws.flatMap (fun w => List.ofFn (fun i : Fin 8 => w.extractLsb' (8 * i.val) 8)) := by
    rw [hauxE_split]; rfl
  rw [henc_eq, split_random_hi8 (StackLayout.of img inputs).randomAddr hrand16]
  have hpure :
      (∀ e ∈ prePairs, e.1 ≠ 0#64 ∧ e.1 ≠ 25#64) ∧
      (∀ e ∈ sufPairs, e.1 ≠ 0#64 ∧ e.1 ≠ 25#64) ∧
      prePairs.length + sufPairs.length ≤ 64 ∧
      (StackLayout.of img inputs).auxvTableAddr.toNat + 16 * (prePairs.length + sufPairs.length + 2) ≤ 2 ^ 48 ∧
      (StackLayout.of img inputs).randomAddr.toNat + 16 ≤ 2 ^ 48 ∧
      (inputs.init.auxv.randomBytes.drop 8).length = 8 :=
    ⟨hpre_no, hsuf_no, hps_le, by omega, by omega, by simp [hrand16]⟩
  have hwords := pointsToBytes_flatMap_u64 (a := (StackLayout.of img inputs).auxvTableAddr) ws
    (by omega) (by rw [hws_len]; omega)
  refine Entails.trans (sepConj_mono_left hwords) ?_
  refine Entails.trans
    (Q := (((StackLayout.of img inputs).auxvTableAddr ↦₆₄* ws) ∗
        (((StackLayout.of img inputs).randomAddr + 8#64) ↦ₛ inputs.init.auxv.randomBytes.drop 8)) ∗
      ((StackLayout.of img inputs).randomAddr ↦ₛ inputs.init.auxv.randomBytes.take 8))
    (by sep_entail) ?_
  unfold MallocngAuxvAt
  exact sepConj_mono_left
    (Entails.sepExists_right prePairs
      (Entails.sepExists_right sufPairs
        (Entails.sepExists_right (StackLayout.of img inputs).randomAddr
          (Entails.sepExists_right 0#64
            (Entails.sepExists_right (inputs.init.auxv.randomBytes.drop 8)
              (by dsimp only [ws]; rw [pure_sepConj_of_true hpure]; sep_entail))))))

private theorem strip_codeLoaded_f3 {prog : Program} {m : Memory} (hL : prog.CodeLoaded m) :
    prog.CodeLoaded (stripExecOutside (progKeep prog) m) := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  have hno := hL.no_wrap
  have hsub : prog.base + BitVec.ofNat 64 i - prog.base = BitVec.ofNat 64 i := by bv_omega
  have hin : progKeep prog (prog.base + BitVec.ofNat 64 i) = true := by
    simp only [progKeep, decide_eq_true_eq, hsub, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    exact hi
  rw [strip_read8, strip_perm_of_keep hin, strip_isLazyFree]
  exact ⟨hL.byte_eq i hi, hL.perm_eq i hi, hL.isLazyFree_eq i hi⟩

private theorem codeLoaded_unstrip_f3 {prog : Program} {m : Memory}
    (hL : prog.CodeLoaded (stripExecOutside (progKeep prog) m)) :
    prog.CodeLoaded m := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  have hno := hL.no_wrap
  have hsub : prog.base + BitVec.ofNat 64 i - prog.base = BitVec.ofNat 64 i := by bv_omega
  have hin : progKeep prog (prog.base + BitVec.ofNat 64 i) = true := by
    simp only [progKeep, decide_eq_true_eq, hsub, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    exact hi
  have hb := hL.byte_eq i hi
  have hp := hL.perm_eq i hi
  have hlf := hL.isLazyFree_eq i hi
  rw [strip_read8] at hb
  rw [strip_perm_of_keep hin] at hp
  rw [strip_isLazyFree] at hlf
  exact ⟨hb, hp, hlf⟩

private theorem holdsBytes_rw_strip (keep : BitVec 64 → Bool) {m : Memory} {addr : BitVec 64}
    {bs : List (BitVec 8)} (h : Obj.HoldsBytes m addr bs (fun _ => Perm.rw)) :
    Obj.HoldsBytes (stripExecOutside keep m) addr bs (fun _ => Perm.rw) := fun i hi => by
  obtain ⟨hb, hp, hlf⟩ := h i hi
  exact ⟨by rw [strip_read8]; exact hb,
    (strip_perm_props keep m _).2.2.2.mpr hp,
    by rw [strip_isLazyFree]; exact hlf⟩

private theorem initialStackInfo_strip (keep : BitVec 64 → Bool) {img : ElfImage}
    {inputs : ProcessInputs} {s0 : State}
    (h : InitialStackInfo img inputs s0) :
    InitialStackInfo img inputs (stripS keep s0) where
  s0_pc := by dsimp [stripS, State.setMem]; exact h.s0_pc
  s0_sp := by dsimp [stripS, State.setMem]; exact h.s0_sp
  s0_regs := by dsimp [stripS, State.setMem]; exact h.s0_regs
  s0_vregs := by dsimp [stripS, State.setMem]; exact h.s0_vregs
  s0_pstate := by dsimp [stripS, State.setMem]; exact h.s0_pstate
  s0_status := by dsimp [stripS, State.setMem]; exact h.s0_status
  s0_tpidrEl0 := by dsimp [stripS, State.setMem]; exact h.s0_tpidrEl0
  s0_brk := by dsimp [stripS, State.setMem]; exact h.s0_brk
  s0_brkStart := by dsimp [stripS, State.setMem]; exact h.s0_brkStart
  s0_fs := by dsimp [stripS, State.setMem]; exact h.s0_fs
  s0_trace := by dsimp [stripS, State.setMem]; exact h.s0_trace
  s0_oracle := by dsimp [stripS, State.setMem]; exact h.s0_oracle
  s0_oracleIdx := by dsimp [stripS, State.setMem]; exact h.s0_oracleIdx
  s0_exclFails := by dsimp [stripS, State.setMem]; exact h.s0_exclFails
  s0_sigActions := by dsimp [stripS, State.setMem]; exact h.s0_sigActions
  s0_sigAltStack := by dsimp [stripS, State.setMem]; exact h.s0_sigAltStack
  s0_physMemAvail := by dsimp [stripS, State.setMem]; exact h.s0_physMemAvail
  sp0_align16 := h.sp0_align16
  random_align16 := h.random_align16
  stackTop_align := h.stackTop_align
  stackBase_floor := h.stackBase_floor
  sp0_headroom := h.sp0_headroom
  argc_bounds := h.argc_bounds
  argvAddrs_eq := h.argvAddrs_eq
  envpAddrs_eq := h.envpAddrs_eq
  upperStr_eq := h.upperStr_eq
  auxvEntries_eq := h.auxvEntries_eq
  addrs_nat := h.addrs_nat
  s0_perm_rw_below_sp0 := fun a h1 h2 => by
    dsimp [stripS, State.setMem]
    exact (strip_perm_props keep s0.mem a).2.2.2.mpr (h.s0_perm_rw_below_sp0 a h1 h2)
  s0_isLazyFree := fun a => by
    dsimp [stripS, State.setMem]; rw [strip_isLazyFree]; exact h.s0_isLazyFree a
  s0_unmapped_heap := fun a h1 h2 => by
    dsimp [stripS, State.setMem]; rw [strip_perm, h.s0_unmapped_heap a h1 h2]; rfl
  s0_mapped_iff := fun a hm => by
    dsimp [stripS, State.setMem] at hm
    change ((stripExecOutside keep s0.mem).perm a).mapped = true at hm
    rw [(strip_perm_props keep s0.mem a).2.2.1] at hm
    exact h.s0_mapped_iff a hm
  holds_argc := holdsBytes_rw_strip keep h.holds_argc
  holds_argv := holdsBytes_rw_strip keep h.holds_argv
  holds_envp := holdsBytes_rw_strip keep h.holds_envp
  holds_auxv := holdsBytes_rw_strip keep h.holds_auxv
  holds_random := holdsBytes_rw_strip keep h.holds_random
  holds_platform := holdsBytes_rw_strip keep h.holds_platform
  holds_upperStr := holdsBytes_rw_strip keep h.holds_upperStr

private theorem codeLoaded_withSvc_iff {P : Program} {svc : State → State} {m : Memory} :
    (P.withSvc svc).CodeLoaded m ↔ P.CodeLoaded m := by
  simp [Program.codeLoaded_iff, Program.withSvc]

private theorem f3Exit80_of_layout {L : StdBinaryLayout} {elf : ElfImage} {P : Program}
    (lf : F3LayoutImageFacts L)
    (hc : F3StartupCode (L.rxProgram elf) L)
    (hsvc : P.svc = Syscall.standard)
    (hHookFree : ∀ pc, progKeep (L.rxProgram elf) pc = true → (P.externAt? pc).isNone = true)
    (fs0 : FsState)
    {sm sr : State}
    (hL_rx : (L.rxProgram elf).CodeLoaded sr.mem)
    (hlr_sm : sm.readReg64 .lr = L.libcStartMainStage2Addr + 56#64)
    (hal_sm : sm.spAligned = true)
    (hret : Returned sm sr)
    (hm_sr : sr.mem ⊨ stackAt sm.sp 80 ∗ StdMuslExitGlobals L 0#8 ∗ anyHeap) :
    ∃ sx : State, Steps P sr sx ∧
      sx.status = .Exited (((sr.readReg64 .x0).setWidth 32).signExtend 64) ∧
      sx.fs = sr.fs ∧ sx.trace = sr.trace := by
  let P_rx := L.rxProgram elf
  let P_st := P_rx.withSvc f3SetTidOnlySvc
  obtain ⟨hpc_sr, hsp_sr, hrun_sr⟩ := hret
  have hal_sr : sr.spAligned = true := by
    simp only [State.spAligned, hsp_sr] at hal_sm ⊢; exact hal_sm
  rw [hlr_sm] at hpc_sr
  have hm_sr' : (sr.setFs fs0).mem ⊨
      (StdMuslExitGlobals L 0#8 ∗ stackAt sm.sp 80) ∗ anyHeap :=
    Satisfies.mono (by sep_entail) hm_sr
  obtain ⟨R_view, hstrip_sat, _⟩ := strip_frame (progKeep P_rx) hm_sr'
  let sr' := stripS (progKeep P_rx) (sr.setFs fs0)
  have hwp_exit : SepWP P_st (L.sysExitAddr + 12#64) sr'
      ((StdMuslExitGlobals L 0#8 ∗ stackAt sm.sp 80) ∗ emp)
      (fun sf' _ => sf'.pc = L.sysExitAddr + 12#64 ∧ sf'.status = .Running ∧
        sf'.readReg64 .x8 = 94#64 ∧
        sf'.readReg64 .x0 = (sr'.readReg32 .x0).signExtend 64 ∧
        sf'.trace = sr'.trace) := by
    rw [sepConj_assoc]
    refine muslExit_to_svc_wp (P := P_st) (L := L) (F := emp)
      hc.muslExit
      (show sr'.pc = L.libcStartMainStage2Addr + 56#64 from hpc_sr)
      (show sr'.status = .Running from hrun_sr)
      (show sr'.sp = sm.sp from hsp_sr)
      (show sr'.spAligned = true from hal_sr)
      lf.finiArray_bnd lf.al_got lf.al_fini lf.al_ofl lf.al_stdin lf.al_stdout
      lf.al_stderrUsed lf.al_stderrFile lf.stderrFile_nz
      fun sf' hpc' hrun' _ _ hx8' hx0' hstd' => ?_
    apply SepWP.done hpc' hrun'
    exact ⟨hpc', hrun', hx8', hx0', hstd'.2.1⟩
  have hL_st : P_st.CodeLoaded sr'.mem := codeLoaded_withSvc_iff.mpr (strip_codeLoaded_f3 hL_rx)
  have hsat_exit : sr'.mem ⊨ ((StdMuslExitGlobals L 0#8 ∗ stackAt sm.sp 80) ∗ emp) ∗ R_view := by
    dsimp only [sr', stripS, State.setMem, State.setFs]
    exact Satisfies.mono (by sep_entail) hstrip_sat
  obtain ⟨s_svc', hsteps_st, ⟨hpc_svc', hrun_svc', _, _, ⟨_, _, hx8_svc', hx0_svc', htr_svc'⟩⟩ | ⟨_, hfalse⟩⟩ :=
    SepWP.to_reaches_pc hwp_exit hsat_exit hL_st
  · obtain ⟨s_svc, hsteps_P, hs_svc_eq, hfs_svc, _, _⟩ :=
      steps_lift_setTidOnly hc.no_hooks hsvc hHookFree hsteps_st hrun_svc' sr fs0 rfl
    have hpc_svc : s_svc.pc = L.sysExitAddr + 12#64 := by
      have := congrArg State.pc hs_svc_eq
      simpa [stripS, State.setFs] using this.symm.trans hpc_svc'
    have hrun_svc : s_svc.status = .Running := by
      have := congrArg State.status hs_svc_eq
      simpa [stripS, State.setFs] using this.symm.trans hrun_svc'
    have hx8_svc : s_svc.readReg64 .x8 = 94#64 := by
      have : s_svc'.readReg64 .x8 = s_svc.readReg64 .x8 := by rw [hs_svc_eq]; rfl
      exact this.symm.trans hx8_svc'
    have hx0_svc : s_svc.readReg64 .x0 = ((sr.readReg64 .x0).setWidth 32).signExtend 64 := by
      have h1 : s_svc'.readReg64 .x0 = s_svc.readReg64 .x0 := by rw [hs_svc_eq]; rfl
      have h2 : sr'.readReg32 .x0 = (sr.readReg64 .x0).setWidth 32 := rfl
      rw [← h1, hx0_svc', h2]
    have htr_svc : s_svc.trace = sr.trace := by
      have h1 : s_svc'.trace = s_svc.trace := by rw [hs_svc_eq]; rfl
      have h2 : sr'.trace = sr.trace := rfl
      exact h1.symm.trans (htr_svc'.trans h2)
    have hL_svc_st : P_rx.CodeLoaded s_svc'.mem := codeLoaded_withSvc_iff.mp (hsteps_st.codeLoaded hL_st)
    have hL_svc_rx : P_rx.CodeLoaded s_svc.mem := by
      rw [hs_svc_eq] at hL_svc_st
      exact codeLoaded_unstrip_f3 hL_svc_st
    have hfetch_rx : P_rx.fetch (L.sysExitAddr + 12#64) = some (.system false 0#16) :=
      MuslExitCode.fetch_sysExit_svc hc.muslExit
    have hfm_rx : P_rx.fetchMem s_svc.mem (L.sysExitAddr + 12#64) =
        some (.system false 0#16) :=
      Program.fetchMem_of_fetch hL_svc_rx hfetch_rx
    have hkeep_sys : progKeep P_rx (L.sysExitAddr + 12#64) = true := by
      unfold Program.fetch Program.readWordOff at hfetch_rx
      rw [hc.no_hooks (L.sysExitAddr + 12#64)] at hfetch_rx
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfetch_rx
      split at hfetch_rx
      · simp at hfetch_rx
      · generalize hd : P_rx.code.drop (L.sysExitAddr + 12#64 - P_rx.base).toNat = bs at hfetch_rx
        match bs with
        | b0 :: b1 :: b2 :: b3 :: _ =>
          have hlen := congrArg List.length hd
          simp only [List.length_drop, List.length_cons] at hlen
          simp only [progKeep, decide_eq_true_eq]
          omega
        | [] | [_] | [_, _] | [_, _, _] => simp at hfetch_rx
    have hfm_P : P.fetchMem s_svc.mem s_svc.pc = some (.system false 0#16) := by
      rw [hpc_svc]
      have hext_P : P.externAt? (L.sysExitAddr + 12#64) = none :=
        Option.isNone_iff_eq_none.mp (hHookFree _ hkeep_sys)
      have hext_rx : P_rx.externAt? (L.sysExitAddr + 12#64) = none :=
        hc.no_hooks _
      simp only [Program.fetchMem, hext_P, hext_rx] at hfm_rx ⊢
      exact hfm_rx
    let sx := P.evalInst (.system false 0#16) s_svc
    have hstep1 : Step P s_svc sx := Step.exec hrun_svc hfm_P
    have hsvc_exit : P.svc s_svc = execExit s_svc := by
      rw [hsvc]
      dsimp only [Syscall.standard, Syscall.dispatch]
      rw [hx8_svc]
      change (match Syscall.standardTable.find? (·.1 == 94#64) with
        | some (_, h) => h s_svc
        | none => s_svc.setStatus (.Exception "unmodeled syscall (svc)")) = execExit s_svc
      rw [show Syscall.standardTable.find? (·.1 == 94#64) = some (94#64, execExit) from rfl]
    refine ⟨sx, hsteps_P.trans (Steps.step hstep1 (Steps.refl _)), ?_, ?_, ?_⟩
    · simp only [sx, Program.evalInst, execInstWithSvc, evalSvc,
        beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
      rw [hsvc_exit]
      dsimp only [execExit, State.setStatus]
      rw [hx0_svc]
    · simp only [sx, Program.evalInst, execInstWithSvc, evalSvc,
        beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
      rw [hsvc_exit]; exact hfs_svc
    · simp only [sx, Program.evalInst, execInstWithSvc, evalSvc,
        beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
      rw [hsvc_exit]; exact htr_svc
  · exact False.elim (not_satisfies_false_sepConj hfalse)

private def lookupKeyIdxF3 : List String → String → Option Nat
  | [], _ => none
  | k :: ks, s => if k == s then some 0 else (lookupKeyIdxF3 ks s).map Nat.succ

private theorem lookup_zip_eq_map_f3 {α : Type} (d : α) :
    ∀ (keys : List String) (vals : List α) (s : String),
      keys.length ≤ vals.length →
      (List.zip keys vals).lookup s = (lookupKeyIdxF3 keys s).map (fun i => vals.getD i d)
  | [], _, _, _ => rfl
  | _ :: _, [], _, h => absurd h (Nat.not_le_of_gt (Nat.succ_pos _))
  | k :: ks, v :: vs, s, h => by
    simp only [List.zip_cons_cons, List.lookup, lookupKeyIdxF3]
    have hcomm : (s == k) = (k == s) := BEq.comm
    rw [hcomm]
    cases hs : k == s
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [lookup_zip_eq_map_f3 d ks vs s (Nat.le_of_succ_le_succ h)]
      cases lookupKeyIdxF3 ks s <;> rfl
    · rfl

private noncomputable def cliHookValsF3 (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    List (State → State) :=
  (CryptoVerification.SignalSession.cliHookTablePlaced mmpl W).map Prod.snd

private theorem cliHookTablePlaced_eq_zip_f3 (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    CryptoVerification.SignalSession.cliHookTablePlaced mmpl W =
      List.zip ElfCodeMatchesData.lsHookNamesPlaced (cliHookValsF3 mmpl W) := by
  rfl_kernel

private theorem lsHookNamesPlaced_eq_fst_f3 (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    ElfCodeMatchesData.lsHookNamesPlaced =
      (CryptoVerification.SignalSession.cliHookTablePlaced mmpl W).map Prod.fst := by
  rfl_kernel

private theorem lsHookNamesPlaced_len_f3 (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    ElfCodeMatchesData.lsHookNamesPlaced.length ≤ (cliHookValsF3 mmpl W).length := by
  rw [lsHookNamesPlaced_eq_fst_f3 mmpl W, cliHookValsF3, List.length_map, List.length_map]

private noncomputable def placedExternTagF3 (s : String) : Option Nat :=
  if CryptoVerification.SignalSession.isCliPanicSymbolPlaced s then some 0
  else (lookupKeyIdxF3 ElfCodeMatchesData.lsHookNamesPlaced s).map Nat.succ

private noncomputable def evalCliTagF3 (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    Nat → State → State
  | 0 => CryptoVerification.SignalSession.abortOnPanic Rust.panicked
  | k + 1 => CryptoVerification.SignalSession.abortOnPanic ((cliHookValsF3 mmpl W).getD k Rust.panicked)

private theorem cliExternsPlacedSig_eq_tag_f3 (mmpl : Obj.MultiPlacement) (W : CliHooks)
    (s : String) :
    CryptoVerification.SignalSession.cliExternsPlacedSig mmpl W s =
      (placedExternTagF3 s).map (evalCliTagF3 mmpl W) := by
  unfold CryptoVerification.SignalSession.cliExternsPlacedSig cliExternsPlaced placedExternTagF3
  cases CryptoVerification.SignalSession.isCliPanicSymbolPlaced s
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [cliHookTablePlaced_eq_zip_f3 mmpl W,
      lookup_zip_eq_map_f3 Rust.panicked _ _ s (lsHookNamesPlaced_len_f3 mmpl W)]
    cases lookupKeyIdxF3 ElfCodeMatchesData.lsHookNamesPlaced s <;> rfl
  · rfl

private theorem findSome_map_val_f3 {α β γ : Type} (f : β → γ) :
    ∀ (L : List α) (g : α → Option β),
      L.findSome? (fun x => (g x).map f) = (L.findSome? g).map f
  | [], _ => rfl
  | x :: xs, g => by
    simp only [List.findSome?_cons]
    cases g x <;> simp [findSome_map_val_f3 f xs g]

private theorem list_findSome_congr_f3 {α β : Type} {l : List α} {f g : α → Option β}
    (h : ∀ x ∈ l, f x = g x) : l.findSome? f = l.findSome? g := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.findSome?_cons, h a List.mem_cons_self]
    cases g a with
    | none => exact ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    | some _ => rfl

private noncomputable def placedTagAtF3 (pc : BitVec 64) : Option Nat :=
  ElfCodeMatchesData.lsPlacedStubPairs.findSome? fun (n, a) =>
    if a == pc then placedExternTagF3 n else none

private theorem placedTagAt_eq_sharedExterns_f3 (pc : BitVec 64) :
    placedTagAtF3 pc = ElfCodeMatchesData.lsSharedExterns.findSome? (fun idx =>
      if ElfCodeMatchesData.f3LsSymAddrs.getD idx 0#64 == pc then
        placedExternTagF3 (ElfCodeMatchesData.lsInternedMultiLib.names.getD idx "")
      else none) := by
  unfold placedTagAtF3
  rw [ElfCodeMatchesData.lsPlacedStubPairs_eq, List.findSome?_map]
  rfl

private theorem cliProgPlacedSig_f3Ls_externAt_tag_f3 (mmpl : Obj.MultiPlacement) (W : CliHooks)
    (pc : BitVec 64) :
    (cliProgPlacedSig ElfCodeMatchesPlaced.f3LsMpl mmpl W).externAt? pc =
      (placedTagAtF3 pc).map (evalCliTagF3 mmpl W) := by
  rw [placedTagAt_eq_sharedExterns_f3, ElfCodeMatchesPlaced.externAt?_cliProgPlacedSig,
    ElfCodeMatchesData.ls_block617_externs_eq, List.findSome?_map]
  have hstep : (ElfCodeMatchesData.lsSharedExterns.findSome? (Function.comp
      (fun e => if libsignalSessionLib.resolve ElfCodeMatchesPlaced.f3LsMpl e == pc then
        CryptoVerification.SignalSession.cliExternsPlacedSig mmpl W e else none)
      (fun idx => ElfCodeMatchesData.lsInternedMultiLib.names.getD idx ""))) =
      ElfCodeMatchesData.lsSharedExterns.findSome? (fun idx =>
        ((if ElfCodeMatchesData.f3LsSymAddrs.getD idx 0#64 == pc then
          placedExternTagF3 (ElfCodeMatchesData.lsInternedMultiLib.names.getD idx "") else none)).map
          (evalCliTagF3 mmpl W)) := by
    refine list_findSome_congr_f3 (l := ElfCodeMatchesData.lsSharedExterns) fun idx hidx => ?_
    dsimp only [Function.comp_def]
    have hlt : idx < ElfCodeMatchesData.lsInternedMultiLib.names.length :=
      Nat.blt_eq.mp (List.all_eq_true.mp ElfCodeMatchesData.ls_sharedExterns_lt idx hidx)
    have hres : libsignalSessionLib.resolve ElfCodeMatchesPlaced.f3LsMpl
        (ElfCodeMatchesData.lsInternedMultiLib.names.getD idx "") =
        ElfCodeMatchesData.f3LsSymAddrs.getD idx 0#64 := by
      rw [ElfCodeMatchesData.ls_toMultiPlacedLib_eq]
      change ElfCodeMatchesData.lsInternedMultiLib.toMultiPlacedLib.resolve
        (ElfCodeMatchesData.f3LsLayout.toMultiPlacement ElfCodeMatchesData.lsInternedMultiLib.names) _ = _
      rw [Obj.Interned.toMultiPlacement_resolve_eq ElfCodeMatchesData.ls_names_nodup
        ElfCodeMatchesData.ls_idsOk ElfCodeMatchesData.ls_blockSymsMatch_ok,
        Obj.Interned.idxOf_getD ElfCodeMatchesData.ls_names_nodup hlt]
      rfl
    rw [hres, cliExternsPlacedSig_eq_tag_f3]
    cases ElfCodeMatchesData.f3LsSymAddrs.getD idx 0#64 == pc <;> rfl
  rw [hstep, findSome_map_val_f3]

private def panicPrefixCharsF3 : List Char :=
  ['c', 'o', 'r', 'e', ':', ':', 'p', 'a', 'n', 'i', 'c', 'k', 'i', 'n', 'g', ':', ':']

private theorem core_panicking_toList_eq_f3 : "core::panicking::".toList = panicPrefixCharsF3 := by
  rfl_kernel

private def isPanicSymbolFastF3 (name : String) : Bool :=
  List.isPrefixOf panicPrefixCharsF3 name.toList ||
  [ "core::result::unwrap_failed",
    "core::option::unwrap_failed",
    "core::option::expect_failed",
    "core::slice::index::slice_start_index_len_fail",
    "core::slice::index::slice_end_index_len_fail",
    "core::slice::index::slice_index_order_fail",
    "core::slice::index::slice_index_fail",
    "alloc::raw_vec::handle_error",
    "alloc::raw_vec::capacity_overflow",
    "alloc::alloc::handle_alloc_error" ].contains name

private theorem isPanicSymbol_eq_fast_f3 (name : String) :
    Rust.isPanicSymbol name = isPanicSymbolFastF3 name := by
  unfold Rust.isPanicSymbol isPanicSymbolFastF3
  have hsw : name.startsWith "core::panicking::" =
      List.isPrefixOf "core::panicking::".toList name.toList := by
    rw [Bool.eq_iff_iff, String.startsWith_string_iff, List.isPrefixOf_iff_prefix]
  rw [hsw, core_panicking_toList_eq_f3]

private noncomputable def placedExternTagFastF3 (s : String) : Option Nat :=
  if CryptoVerification.SignalSession.cliPanicSymbolsPlaced.contains s || isPanicSymbolFastF3 s then some 0
  else (lookupKeyIdxF3 ElfCodeMatchesData.lsHookNamesPlaced s).map Nat.succ

private theorem placedExternTag_eq_fast_f3 (s : String) :
    placedExternTagF3 s = placedExternTagFastF3 s := by
  unfold placedExternTagF3 placedExternTagFastF3 CryptoVerification.SignalSession.isCliPanicSymbolPlaced
  rw [isPanicSymbol_eq_fast_f3]

private def lookupAddrTagF3 (tbl : List (BitVec 64 × Option Nat)) (pc : BitVec 64) : Option Nat :=
  tbl.findSome? fun (a, t) => if a == pc then t else none

private noncomputable def lsPlacedTagTableF3 : List (BitVec 64 × Option Nat) :=
  ElfCodeMatchesData.lsPlacedStubPairs.map fun (n, a) => (a, placedExternTagFastF3 n)

private theorem placedTagAt_eq_table_f3 (pc : BitVec 64) :
    placedTagAtF3 pc = lookupAddrTagF3 lsPlacedTagTableF3 pc := by
  unfold placedTagAtF3 lookupAddrTagF3 lsPlacedTagTableF3
  rw [List.findSome?_map]
  refine list_findSome_congr_f3 (l := ElfCodeMatchesData.lsPlacedStubPairs) fun ⟨n, a⟩ _ => ?_
  dsimp only [Function.comp_def]
  rw [placedExternTag_eq_fast_f3]

private def compactTagTblF3 : List (BitVec 64 × Option Nat) → List (Nat × Nat)
  | [] => []
  | (_, none) :: xs => compactTagTblF3 xs
  | (a, some t) :: xs => (a.toNat, t) :: compactTagTblF3 xs

private def lookupAddrTagNatF3 : List (Nat × Nat) → Nat → Option Nat
  | [], _ => none
  | (a, t) :: xs, pc => if Nat.beq a pc then some t else lookupAddrTagNatF3 xs pc

private theorem bv64_beq_eq_nat_beq_f3 (a b : BitVec 64) : (a == b) = Nat.beq a.toNat b.toNat := by
  cases h : a == b
  · symm
    rw [Bool.eq_false_iff]
    intro h'
    rw [Nat.beq_eq] at h'
    exact absurd (beq_iff_eq.mpr (BitVec.eq_of_toNat_eq h')) (by simp [h])
  · rw [beq_iff_eq] at h
    subst h
    exact (Nat.beq_refl _).symm

private theorem lookupAddrTag_eq_compact_f3 :
    ∀ (tbl : List (BitVec 64 × Option Nat)) (pc : BitVec 64),
      lookupAddrTagF3 tbl pc = lookupAddrTagNatF3 (compactTagTblF3 tbl) pc.toNat
  | [], _ => rfl
  | (_, none) :: xs, pc => by
    simp only [lookupAddrTagF3, compactTagTblF3, List.findSome?_cons, ite_self]
    exact lookupAddrTag_eq_compact_f3 xs pc
  | (a, some t) :: xs, pc => by
    simp only [lookupAddrTagF3, compactTagTblF3, lookupAddrTagNatF3, List.findSome?_cons]
    rw [bv64_beq_eq_nat_beq_f3 a pc]
    cases Nat.beq a.toNat pc.toNat
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact lookupAddrTag_eq_compact_f3 xs pc
    · rfl

set_option maxRecDepth 4000000 in
private theorem lsPlacedTagTable_eq_lit_f3 :
    lsPlacedTagTableF3 = ElfCodeMatchesData.lsPlacedTagTableLit := by
  rfl_kernel

set_option maxRecDepth 4000000 in
private theorem compactTagTbl_placed_eq_lit_f3 :
    compactTagTblF3 ElfCodeMatchesData.lsPlacedTagTableLit = ElfCodeMatchesData.lsPlacedCompactLit := by
  rfl_kernel

private theorem lookupAddrTagNat_none_of_all_lt_f3 :
    ∀ (xs : List (Nat × Nat)) (pc : Nat),
      (xs.all fun p => Nat.blt p.1 pc) = true →
      lookupAddrTagNatF3 xs pc = none
  | [], _, _ => rfl
  | (a, t) :: xs, pc, hall => by
    simp only [List.all_cons, Bool.and_eq_true, Nat.blt_eq] at hall
    have hne : Nat.beq a pc = false := by
      rw [Bool.eq_false_iff, Ne, Nat.beq_eq]
      omega
    simp only [lookupAddrTagNatF3, hne, Bool.false_eq_true, ↓reduceIte]
    exact lookupAddrTagNat_none_of_all_lt_f3 xs pc hall.2

set_option maxRecDepth 4000000 in
private theorem lsPlacedCompactLit_lt_rxSegBase :
    (ElfCodeMatchesData.lsPlacedCompactLit.all fun p =>
      Nat.blt p.1 Tie.f3RxSegBase.toNat) = true := by
  rfl_kernel

private theorem f3ProgExt_hookFree_in_rxSeg {mpl mmpl : Obj.MultiPlacement}
    (hls : libsignalSessionLib.LinkedAt cliElfBytes mpl) (W : CliHooks) :
    ∀ pc, progKeep (f3StdLayout.rxProgram f3PatchedElf) pc = true →
      ((cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc).isNone =
        true := by
  obtain ⟨_, hp, hpl, hin⟩ := hls
  cases cliElf_parse.symm.trans hp
  intro pc hkeep
  rw [f3PatchedElf_rxProgram_eq] at hkeep
  simp only [progKeep, Tie.f3TrialRxProg_base, decide_eq_true_eq] at hkeep
  have hcode_lt : Tie.f3TrialRxProg.code.length < 2 ^ 64 := by
    have hs := Tie.f3TrialRxWordTree_size
    have hl : Tie.f3TrialRxProg.code.length = 4 * LibsignalBinary.Heap.Fine.f3RxWordCount := by
      rw [Tie.f3TrialRxWordTree_eq, WordTree.length_toBytes_of_checkSize? hs]
    rw [hl]; decide
  have hbase_hi : Tie.f3RxSegBase.toNat + Tie.f3TrialRxProg.code.length ≤ 2 ^ 64 := by
    have hrx_bnd : Tie.f3RxSegBase.toNat < 2 ^ 48 := by decide
    have hlen_bnd : Tie.f3TrialRxProg.code.length < 2 ^ 30 := by
      have hs := Tie.f3TrialRxWordTree_size
      have hl : Tie.f3TrialRxProg.code.length = 4 * LibsignalBinary.Heap.Fine.f3RxWordCount := by
        rw [Tie.f3TrialRxWordTree_eq, WordTree.length_toBytes_of_checkSize? hs]
      rw [hl]; decide
    omega
  have hge_rx : Tie.f3RxSegBase.toNat ≤ pc.toNat := by
    by_contra hlt_pc
    have hlt' : pc.toNat < Tie.f3RxSegBase.toNat := Nat.lt_of_not_ge hlt_pc
    have hsub : (pc - Tie.f3RxSegBase).toNat = 2 ^ 64 + pc.toNat - Tie.f3RxSegBase.toNat := by
      bv_omega
    omega
  have hall : (ElfCodeMatchesData.lsPlacedCompactLit.all fun p => Nat.blt p.1 pc.toNat) = true := by
    rw [List.all_eq_true]
    intro p hp_mem
    have hlt := Nat.blt_eq.mp (List.all_eq_true.mp lsPlacedCompactLit_lt_rxSegBase p hp_mem)
    rw [Nat.blt_eq]
    omega
  have hnone_cmp : lookupAddrTagNatF3 ElfCodeMatchesData.lsPlacedCompactLit pc.toNat = none :=
    lookupAddrTagNat_none_of_all_lt_f3 ElfCodeMatchesData.lsPlacedCompactLit pc.toNat hall
  have hsig_none : (cliProgPlacedSig mpl mmpl W).externAt? pc = none := by
    rw [ElfCodeMatchesPlaced.cliProgPlacedSig_externAt_eq_of_inElf hpl hin mmpl W pc,
      cliProgPlacedSig_f3Ls_externAt_tag_f3, placedTagAt_eq_table_f3,
      lsPlacedTagTable_eq_lit_f3, lookupAddrTag_eq_compact_f3,
      compactTagTbl_placed_eq_lit_f3, hnone_cmp]
    rfl
  rw [← cliProgExtPlacedSigAt_cliExternsPlaced_eq,
    externAt?_cliProgExtPlacedSigAt_eq_none] at hsig_none
  rw [hsig_none]; rfl

set_option maxRecDepth 4000000 in
private theorem cliElf_base617_eq_cMainAddr :
    ElfCodeMatchesPlaced.f3LsMpl.base 617 = f3StdLayout.cMainAddr := by
  rfl_kernel

private theorem mpl_base617_eq_cMainAddr_of_linkedAt {mpl : Obj.MultiPlacement}
    (hls : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    mpl.base 617 = f3StdLayout.cMainAddr := by
  have h617 : 617 < libsignalSessionLib.blocks.length := by
    have hlen := Nat.beq_eq.mp ElfCodeMatchesData.libsignalBlocks_len
    have hge : 618 ≤ ElfCodeMatchesData.f3LsBlocksLen := by decide
    omega
  exact ((ElfCodeMatchesPlaced.f3CliElf_libsignal_linkedAt_unique hls).1 617 h617).trans
    cliElf_base617_eq_cMainAddr

set_option maxRecDepth 4000000 in
private theorem cliBudgetLimits_layout_bounds :
    (cliBudgetLimits.enforced = true → f3SegCount + 1 ≤ cliBudgetLimits.staticCount) ∧
    (cliBudgetLimits.enforced = true → cliStackSize + f3SegByteSum ≤ cliBudgetLimits.staticBytes) ∧
    (cliBudgetLimits.enforced = true → cliBudgetLimits.physCap ≤ 2 ^ 30) := by
  exact ⟨fun _ => by decide, fun _ => by decide, fun _ => by decide⟩

theorem cliElf_f3MallocngLayout : CliElfMallocngLayout cliElfImage cliBudgetLimits :=
  Fixture.f3TrialElf_cliElfMallocngLayout
    cliBudgetLimits_layout_bounds.1
    cliBudgetLimits_layout_bounds.2.1
    cliBudgetLimits_layout_bounds.2.2

private theorem startup_argvAtRO_eq_strict_argvAtRO (a : BitVec 64) (xs : List (List (BitVec 8))) :
    argvAtRO a xs =
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.argvAtRO a xs := by
  induction xs generalizing a with
  | nil => rfl
  | cons s ss ih =>
    simp only [argvAtRO, cStrAtRO,
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.argvAtRO,
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.cStrAtRO, ih]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000000 in
/-- `MuslHarnessFineNeedLocksGuardedPerInput` at `StdMainEntryLr f3StdLayout` on
`patchElfTokensPlacedAt mpl cliElfImage` for any `LinkedAt cliElfBytes` placements `(mpl, mmpl)`. -/
theorem cliElf_f3MuslHarnessLr_of_linkedAt {mpl mmpl : Obj.MultiPlacement}
    (hls : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hmng : VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks) :
    MuslHarnessFineNeedLocksGuardedPerInput 80
      (mallocngAddrsOfPlacement mmpl).libc
      (patchElfTokensPlacedAt mpl cliElfImage)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      (mpl.base 617)
      cliProcessInputs
      mmpl cliBudgetLimits fineCostModel.init cliMainStk
      (F3CodeOk mpl mmpl)
      (cliStaticsPlacedAt mpl) (StdMainEntryLr f3StdLayout) := by
  have hlibc_mmpl : (mallocngAddrsOfPlacement mmpl).libc = f3StdLayout.libcAddr := by
    rw [mallocngAddrsOfPlacement_eq_f3_of_linkedAt hmng]
    exact Inst.f3MAddrs_libc
  have hlay_patched : CliElfMallocngLayout
      (patchElfTokensPlacedAt mpl cliElfImage) cliBudgetLimits :=
    (cliElfMallocngLayout_iff_patchElfTokensPlacedAt).mpr cliElf_f3MallocngLayout
  refine muslHarnessFineNeedLocksGuardedPerInput_of_startup
    cliStackShape_cliProcessInputs hlay_patched rfl ?_
  intro _hE i ⟨hi, hl⟩
  let P := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W
  have hpatch_eq := f3PatchedElf_eq_of_linkedAt hls
  have hmatch := f3PatchedElf_matchesImage
  have hc : F3StartupCode (f3StdLayout.rxProgram f3PatchedElf) f3StdLayout := by
    rw [f3PatchedElf_rxProgram_eq]; exact Inst.f3Trial_startupCode
  have hsvc : P.svc = Syscall.standard := rfl
  have hHookFree := f3ProgExt_hookFree_in_rxSeg (mmpl := mmpl) hls W
  let L := f3StdLayout
  let elf := f3PatchedElf
  let inputs0 := f3EmptyFsInputs i
  have hvalid0 : inputs0.Valid := f3EmptyFsInputs_valid hi
  obtain ⟨hwf, hentry_eq, hphdr_eq, hphnum_eq, hbrk_eq, ⟨hbrk_lo, hbrk_hi⟩, _⟩ :=
    f3MatchesImage_segments hmatch
  have hbrk_sbm : elf.brkStart.toNat ≤ STACK_BASE_MIN := by
    rw [hbrk_eq]; unfold STACK_BASE_MIN; omega
  obtain ⟨s0_0, hload0, hinfo0⟩ := loadState_ok_initialStackInfo elf hwf hvalid0 hbrk_sbm
  obtain ⟨s0, hload_c, hs0_0_eq, hfs0, htr0, hmem0, hbrk0, hbrkS0, hphys0⟩ :=
    loadState_f3CliInputs_of_empty hl hload0
  have hload : (patchElfTokensPlacedAt mpl cliElfImage).loadState (cliProcessInputs i) =
      .ok s0 := by
    rw [hpatch_eq]; exact hload_c
  let P_rx := L.rxProgram elf
  let P_st := P_rx.withSvc f3SetTidOnlySvc
  let s0' := stripS (progKeep P_rx) s0_0
  have hinfo' : InitialStackInfo elf inputs0 s0' := initialStackInfo_strip (progKeep P_rx) hinfo0
  have hL0_rx : P_rx.CodeLoaded s0_0.mem := f3MatchesImage_codeLoaded hmatch hload0
  have hL0_st : P_st.CodeLoaded s0'.mem := codeLoaded_withSvc_iff.mpr (strip_codeLoaded_f3 hL0_rx)
  have lf : F3LayoutImageFacts L := extractF3LayoutImageFacts hmatch hload0
  have hextra := hc.extra
  dsimp only [f3StartupExtraChunks, CodeChunks, CodeChunk.holds] at hextra
  obtain ⟨hc_start, hc_startC, hc_lsm, hc_init, hdummy1, hc_stls, hc_ctls, hc_itp, hset_tp,
    hc_st2, hc_lsi, hinitFn, hc_doInit, hc_getaux, hc_det, hc_ilse, hc_enlse⟩ := hextra
  let sl := StackLayout.of elf inputs0
  have hinp0_eq : inputs0 = processInputs ("libsignal-cli" :: i.argv) [] [] [] := rfl
  have hlay := loadState_cli_layout elf i.argv [] [] [] hwf
    (by
      have hbf := hvalid0.stack.base_floor
      have hsb_eq : inputs0.init.stackTop.toNat - inputs0.init.stackSize =
          defaultStackTop.toNat - cliStackSize := rfl
      omega)
    (fun a ha => (hi.1 a ha).2) hi.2 (by simp) (by simp)
  have hs0_raw : s0_0 = elf.rawState inputs0 := by
    have hlay1 : elf.loadState inputs0 = .ok (elf.rawState inputs0) := hinp0_eq ▸ hlay.1
    exact Except.ok.inj (hload0.symm.trans hlay1)
  have hsp0_init : sl.sp0.toNat = sp0 (cliStrs i.argv) := by
    have hsp_bv : sl.sp0 = BitVec.ofNat 64 (sp0 (cliStrs i.argv)) := by
      rw [← hinfo0.s0_sp, hs0_raw]; exact hinp0_eq ▸ hlay.2.1
    rw [hsp_bv, toNat_sp0]
  have hhr8 : inputs0.init.stackTop.toNat - inputs0.init.stackSize + 8371824 ≤ sl.sp0.toNat := by
    have hlo : stackBase + 8371824 ≤ sp0 (cliStrs i.argv) := hlay.2.2.2.1
    have hsb_eq : inputs0.init.stackTop.toNat - inputs0.init.stackSize = stackBase := by
      unfold stackBase cliStackSize; rfl
    omega
  have hsp0_16 := hinfo'.sp0_align16
  have hsp0_ge : 8371824 ≤ sl.sp0.toNat := by omega
  have hscan := auxvScan38_mkAuxvEntries elf hvalid0.auxv sl.platformAddr sl.randomAddr sl.execfnAddr
  rw [← hinfo'.auxvEntries_eq] at hscan
  have hwf_aux := mkAuxvEntries_wf elf hvalid0.auxv sl.platformAddr sl.randomAddr sl.execfnAddr
  rw [← hinfo'.auxvEntries_eq] at hwf_aux
  have hfind_aux := mkAuxvEntries_find? elf hvalid0.auxv sl.platformAddr sl.randomAddr sl.execfnAddr []
  rw [List.append_nil, ← hinfo'.auxvEntries_eq] at hfind_aux
  have hphent_eq := (wellFormed_segments_bounds hwf).1
  have hbrk_mod : elf.brkStart.toNat % 4096 = 0 := (wellFormed_segments_bounds hwf).2.1
  have hTlsSpec : subroutine_ok P_st L.staticInitTlsAddr (f3StaticInitTlsSpec L) :=
    f3StaticInitTls_setTidOnly_ok
      hc_stls hc_ctls hc_itp (show P_st.hasCode L.setThreadAreaAddr setThreadAreaWords from hset_tp)
      hc.memOpsSetTid rfl lf.checkPhdr lf.phdr_end lf.builtinTls_al lf.mainTls_nz
  let sysinfoVal := (auxvScan38 sl.auxvEntries).getD 32 0#64
  have hTls : ∀ (st : State) (FTls : SepProp), st.pc = L.staticInitTlsAddr → st.status = .Running →
      st.sp = sl.sp0 - 448#64 → st.readReg64 .x0 = sl.sp0 - 352#64 →
      st.readReg64 .lr = L.initLibcAddr + 268#64 → StdStatePreserved s0' st →
      SepWP P_st (L.initLibcAddr + 268#64) st
        ((((sl.sp0 - 352#64) ↦₆₄* auxvScan38 sl.auxvEntries) ∗ (L.gotAddr ↦₆₄ 0#64) ∗
          (L.sysinfoAddr ↦₆₄ sysinfoVal) ∗ f3PreTlsSep L sl.sp0) ∗ FTls)
        (fun st' Q => st'.pc = L.initLibcAddr + 268#64 ∧ st'.status = .Running ∧
          st'.sp = sl.sp0 - 448#64 ∧
          (st'.tpidrEl0 = L.builtinTlsAddr + 200#64 ∧ StdTlsFieldsPreserved st st') ∧
          (Q ⊢ (((sl.sp0 - 352#64) ↦₆₄* auxvScan38 sl.auxvEntries) ∗ (L.gotAddr ↦₆₄ 0#64) ∗
            (L.sysinfoAddr ↦₆₄ sysinfoVal) ∗ f3PostTlsSep L sl.sp0 sysinfoVal) ∗ FTls)) := by
    intro st FTls hpct hrunt hspt hx0t hlrt _
    have hsp_al_t : st.spAligned = true := by
      simp only [State.spAligned, hspt, beq_iff_eq]
      have hb : sl.sp0 &&& 15#64 = 0#64 := by
        apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_and]; change sl.sp0.toNat &&& 15 = 0
        rw [Nat.and_two_pow_sub_one_eq_mod _ 4]; exact hsp0_16
      bv_bits
    have hsp_60 : st.sp - 96#64 = sl.sp0 - 544#64 := by rw [hspt]; bv_lin
    refine SepWP.call_subroutine_frame (ret_pc := L.initLibcAddr + 268#64) hTlsSpec
      (x := (sl.sp0 - 352#64, auxvScan38 sl.auxvEntries, 0#8, sysinfoVal)) (F := FTls)
      hpct hrunt hsp_al_t hlrt ?_
      (fun _ _ _ h => not_satisfies_false_sepConj h)
      (fun _ _ _ _ h => not_satisfies_false_sepConj h)
      fun st' hpct' hrunt' hspt' _ => ?_
    · dsimp only [f3StaticInitTlsSpec, f3PreTlsSep]
      rw [hsp_60, pure_sepConj_of_true ⟨hx0t, hphdr_eq ▸ hscan.2.1,
        hphent_eq ▸ hscan.2.2.1, hphnum_eq ▸ hscan.2.2.2.1⟩]
      sep_entail
    · dsimp only [f3StaticInitTlsSpec]
      rw [sepConj_assoc]; apply SepWP.pure_elim; rintro ⟨htp', htls'⟩
      have hspt'' : st'.sp = sl.sp0 - 448#64 := hspt'.trans hspt
      have hsp'_60 : st'.sp - 96#64 = sl.sp0 - 544#64 := by rw [hspt'']; bv_lin
      apply SepWP.done hpct' hrunt'
      refine ⟨hpct', hrunt', hspt'', ⟨htp', htls'⟩, ?_⟩
      dsimp only [f3PostTlsSep]; rw [htp', hsp'_60]; sep_entail
  have hLsiSpec : subroutine_ok P_st L.libcStartInitAddr (stdLibcStartInitSpec L) :=
    libcStartInit_ok P_st L hc_lsi
      (initFn_ok P_st L.initFnAddr hinitFn)
      (initLse_ok P_st L hc_ilse
        (detectAndInitialize_ok P_st L hc_det
          (getauxval_found_ok P_st L hc_getaux))
        (rustEnableLse_ok P_st L hc_enlse))
      (doInit_ok P_st L hc_doInit)
  have hmr_init : memRegion (sl.sp0 - 8371824#64) 8371824 =
      memRegion (sl.sp0 - 8371824#64) 8371280 ∗ memRegion (sl.sp0 - 544#64) 96 ∗
      memRegion (sl.sp0 - 448#64) 448 := by
    have s1 := memRegion_split_le (sl.sp0 - 8371824#64) 8371280 8371824 (by decide) (by decide)
    have s2 := memRegion_split_le (sl.sp0 - 544#64) 96 544 (by decide) (by decide)
    rw [show sl.sp0 - 8371824#64 + BitVec.ofNat 64 8371280 = sl.sp0 - 544#64 by bv_lin] at s1
    rw [show sl.sp0 - 544#64 + BitVec.ofNat 64 96 = sl.sp0 - 448#64 by bv_lin] at s2
    rw [s1, show (8371824 - 8371280 : Nat) = 544 from rfl, s2, show (544 - 96 : Nat) = 448 from rfl]
  have hmr_st2 : memRegion (sl.sp0 - 8371824#64) 8371280 ∗ memRegion (sl.sp0 - 544#64) 96 ∗
      memRegion (sl.sp0 - 448#64) 448 =
      stackAt (sl.sp0 - 304#64) 8371520 ∗ stackFrameAt sl.sp0 304 := by
    rw [← hmr_init, ← stackAt_eq_stackFrameAt sl.sp0 304]
    have s1 := memRegion_split_le (sl.sp0 - 8371824#64) 8371520 8371824 (by decide) (by decide)
    have e1 : sl.sp0 - 8371824#64 + BitVec.ofNat 64 8371520 = sl.sp0 - 304#64 := by bv_lin
    have e2 : (sl.sp0 - 304#64) - BitVec.ofNat 64 8371520 = sl.sp0 - 8371824#64 := by bv_lin
    dsimp only [stackAt]; rw [e1] at s1; rw [e2]; exact s1
  have hwp_startup : SepWP P_st L.cMainAddr s0' (f3InitAllSep L elf inputs0)
      (fun s_cm P_out =>
        (s_cm.sp = sl.sp0 - 48#64 ∧ s_cm.spAligned = true ∧
          cliMainStk ≤ s_cm.sp.toNat ∧
          s_cm.readReg64 .x30 = L.libcStartMainStage2Addr + 56#64 ∧
          s_cm.readReg64 .x0 = BitVec.ofNat 64 inputs0.argv.length ∧
          s_cm.readReg64 .x1 = sl.argvTableAddr ∧
          s_cm.tpidrEl0 = L.builtinTlsAddr + 200#64 ∧
          StdTlsFieldsPreserved s0' s_cm) ∧
        (P_out ⊢ ((L.libcAddr + 3#64) ↦₈ 0#8) ∗
          argvAtRO sl.argvTableAddr inputs0.argv ∗
          stackAt (sl.sp0 - 48#64) cliMainStk ∗
          StdExtraRo L ∗ StdExtraRw L ∗
          ((L.builtinTlsAddr + 200#64 - 164#64) ↦₃₂ 0#32) ∗
          ((L.libcAddr + 8#64) ↦₆₄ sl.auxvTableAddr) ∗
          ((L.libcAddr + 48#64) ↦₆₄ 4096#64) ∗
          MallocngAuxvAt sl.auxvTableAddr ∗
          f3StartupResidual L elf i ∗
          StdMuslExitGlobalsNoNeedLocks L 0#8)) := by
    apply SepWP.cut (mid := L.libcStartMainStage2Addr)
    refine SepWP.weaken_pre (P' := (memRegion (sl.sp0 - 448#64) 448 ∗ Stage1GlobalsPre L ∗
        StdGotGlobals L ∗ (sl.sp0 ↦₆₄ᵣ BitVec.ofNat 64 inputs0.argv.length) ∗
        (sl.argvTableAddr ↦₆₄ᵣ* (sl.argvAddrs ++ [0#64])) ∗
        (sl.envpTableAddr ↦₆₄ᵣ* (sl.envpAddrs ++ [0#64])) ∗
        (sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗
        (sl.argvBase ↦ᵣ sl.upperStrBytes) ∗ f3PreTlsSep L sl.sp0) ∗ _) (by
      rw [f3InitAllSep]
      dsimp only [f3PreTlsSep, F3RoConstants, F3InitGlobals, Stage1GlobalsPre,
        StdLibcGlobals, F3DataGlobals, StdLibcTlsZero,
        StdBinaryLayout.libcAtoms, f3DataNoStderrAtoms, rwAtomListSep, RwAtom.toSepProp]
      rw [rwAtomListSep_f3BssAtoms L, hmr_init]
      sep_frame) ?_
    apply SepWP.mono
    case h =>
      exact muslStage1 hinfo' hvalid0
        hc_start hc_startC hc_lsm hc_init hdummy1 hc.memOpsSetTid
        (by
          intro st FTls hpct hrunt hspt hx0t hlrt hpres
          exact hTls st FTls hpct hrunt hspt hx0t hlrt hpres)
        hentry_eq hc.ne_memset hc.ne_tls hc.ne_stage2
    case hoom => exact fun _ _ _ ho => ho
    case himp =>
    rintro s_st2 _ hpc_st2 hrun_st2 ⟨⟨hsp_st2, hx0_st2, hx1_st2, hx2_st2,
      st, st', hstd0t, ⟨htp_t', htlst⟩, hstdtf⟩, hent_st2⟩
    apply SepWP.weaken_pre hent_st2
    have hsp_al_st2 : s_st2.spAligned = true := by
      simp only [State.spAligned, hsp_st2, beq_iff_eq]
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_and]; change sl.sp0.toNat &&& 15 = 0
      rw [Nat.and_two_pow_sub_one_eq_mod _ 4]; exact hsp0_16
    have htp_st2 : s_st2.tpidrEl0 = L.builtinTlsAddr + 200#64 := hstdtf.2.2.1.trans htp_t'
    have htlf_0_st2 : StdTlsFieldsPreserved s0' s_st2 :=
      (hstd0t.toTlsFields.trans htlst).trans hstdtf.toTlsFields
    have hm_st2 : memRegion (sl.sp0 - 448#64) 448 ∗ memRegion (sl.sp0 - 544#64) 96 ∗
        memRegion (sl.sp0 - 8371824#64) 8371280 =
        stackAt (sl.sp0 - 304#64) 8371520 ∗ stackFrameAt sl.sp0 304 := by
      rw [← hmr_st2]; sep_ac_rfl
    refine SepWP.weaken_pre (P' := (stdInitGlobalsPre L sl.auxvTableAddr sl.auxvEntries ∗
        stackFrameAt sl.sp0 304) ∗ _) (by
      dsimp only [f3PostTlsSep, Stage1GlobalsPost, StdGotGlobals, StdInitFiniGlobals,
        stdInitGlobalsPre, StdBinaryLayout.gotAtoms, StdBinaryLayout.initFiniAtoms,
        rwAtomListSep, RwAtom.toSepProp]
      refine Entails.trans (Q := (memRegion (sl.sp0 - 448#64) 448 ∗
        memRegion (sl.sp0 - 544#64) 96 ∗ memRegion (sl.sp0 - 8371824#64) 8371280) ∗ _)
        (by sep_frame) ?_
      rw [hm_st2]; sep_frame) ?_
    refine stage2_to_cMain P_st L hc_st2 hLsiSpec
      hpc_st2 hrun_st2 hsp_st2 hsp_al_st2
      hx0_st2 hx1_st2 hx2_st2 hinfo'.argc_bounds.2.1 hvalid0.auxv.hwcap_fp_asimd
      (fun t v hm => (hwf_aux.2.2 t v hm).1) hfind_aux.2.2.2.2.2.2.2.2.2.2.1
      hfind_aux.2.2.2.2.2.2.2.2.2.2.2.2.2.1 lf.initArray_bnd
      fun s_cm hpc_cm hrun_cm hsp_cm hsp_al_cm hlr_cm hx0_cm hx1_cm _ hstd_cm => ?_
    dsimp only [stdInitGlobalsPost]
    wp_conv_pre => simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro cacheVal
    have hstk_cm : stackAt (sl.sp0 - 304#64) 8371520 ∗ stackFrameAt (sl.sp0 - 48#64) 256 =
        stackAt (sl.sp0 - 48#64) cliMainStk := by
      rw [← stackAt_eq_stackFrameAt (sl.sp0 - 48#64) 256]
      have c1 := memRegion_split_le (sl.sp0 - 8371824#64) 8371520 cliMainStk (by decide) (by decide)
      rw [show sl.sp0 - 8371824#64 + BitVec.ofNat 64 8371520 = sl.sp0 - 304#64 by bv_lin] at c1
      dsimp only [stackAt, cliMainStk]
      rw [show (sl.sp0 - 304#64) - 8371520#64 = sl.sp0 - 8371824#64 by bv_lin,
        show (sl.sp0 - 48#64) - 256#64 = sl.sp0 - 304#64 by bv_lin,
        show (sl.sp0 - 48#64) - 8371776#64 = sl.sp0 - 8371824#64 by bv_lin]
      exact c1.symm
    have htp_cm : s_cm.tpidrEl0 = L.builtinTlsAddr + 200#64 := hstd_cm.2.2.1.trans htp_st2
    have htlf_0_cm : StdTlsFieldsPreserved s0' s_cm := htlf_0_st2.trans hstd_cm.toTlsFields
    have hsp_cm_ge : cliMainStk ≤ s_cm.sp.toNat := by
      rw [hsp_cm, BitVec.toNat_sub_of_le (by change 48 ≤ sl.sp0.toNat; omega)]
      change 8371776 ≤ sl.sp0.toNat - 48; omega
    have hargv_dup := argvTable_dup_argvAtRO hinfo0 hvalid0.args
    have hauxv_ent := auxv_entails_mallocngAuxvAt hinfo0 hvalid0
    apply SepWP.done hpc_cm hrun_cm
    refine ⟨⟨hsp_cm, hsp_al_cm, hsp_cm_ge, hlr_cm, hx0_cm, hx1_cm, htp_cm, htlf_0_cm⟩, ?_⟩
    dsimp only [StdMuslExitGlobalsNoNeedLocks]
    refine Entails.trans (Q := ((stackAt (sl.sp0 - 304#64) 8371520 ∗
        stackFrameAt (sl.sp0 - 48#64) 256) ∗
      ((sl.argvTableAddr ↦₆₄ᵣ* (sl.argvAddrs ++ [0#64])) ∗ (sl.argvBase ↦ᵣ sl.upperStrBytes)) ∗
      ((sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗
        (sl.randomAddr ↦ₛ inputs0.init.auxv.randomBytes)) ∗ _))
      (by sep_frame) ?_
    rw [hstk_cm]
    refine Entails.trans
      (sepConj_mono_right
        (sepConj_mono hargv_dup (sepConj_mono_left hauxv_ent))) ?_
    unfold f3StartupResidual
    refine Entails.trans (Q := ((L.libcAddr + 3#64) ↦₈ 0#8) ∗
        argvAtRO sl.argvTableAddr inputs0.argv ∗
        stackAt (sl.sp0 - 48#64) cliMainStk ∗
        StdExtraRo L ∗ StdExtraRw L ∗
        ((L.builtinTlsAddr + 200#64 - 164#64) ↦₃₂ 0#32) ∗
        ((L.libcAddr + 8#64) ↦₆₄ sl.auxvTableAddr) ∗
        ((L.libcAddr + 48#64) ↦₆₄ 4096#64) ∗
        MallocngAuxvAt sl.auxvTableAddr ∗
        ((L.finiArrayAddr ↦₆₄ L.doFiniAddr) ∗ ((L.gotAddr + 32#64) ↦₆₄ 0#64) ∗
          ((L.gotAddr + 40#64) ↦₆₄ 0#64) ∗ ((L.gotAddr + 96#64) ↦₆₄ (L.finiArrayAddr + 8#64)) ∗
          ((L.gotAddr + 104#64) ↦₆₄ L.finiArrayAddr) ∗ (L.finalizedAddr ↦₈ 0#8) ∗
          (L.oflHeadAddr ↦₆₄ 0#64) ∗ (L.stdinUsedAddr ↦₆₄ 0#64) ∗
          (if L.stdoutUsedAddr == L.stdinUsedAddr then emp else L.stdoutUsedAddr ↦₆₄ 0#64) ∗
          (L.stderrUsedAddr ↦₆₄ L.stderrFileAddr) ∗ StdStderrFile L) ∗ _)
      (by sep_frame) ?_
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right
            (Entails.sepExists_right (Q := fun R_unused => R_unused) _ (Entails.refl _)))))))))))) ?_
    sep_entail
  have hm0_0 : s0_0.mem ⊨ f3InitAllSep L elf inputs0 ∗ cliStaticsPlacedAt mpl :=
    s0_satisfies_f3InitAllSep_and_statics hls hload0 hinfo0 hvalid0 hhr8
  obtain ⟨R_view, hs0'_sat, hunstrip⟩ := strip_frame (progKeep P_rx) hm0_0
  obtain ⟨s_cm', hsteps_st, ⟨hpc_cm', hrun_cm', P_out, hm_out',
    ⟨hsp_cm', hsp_al_cm', hsp_ge_cm', hlr_cm', hx0_cm', hx1_cm', htp_cm', htlf_cm'⟩,
    hent_out⟩ | ⟨_, hfalse⟩⟩ :=
    SepWP.to_reaches_pc hwp_startup hs0'_sat hL0_st
  · obtain ⟨sm, hsteps_P, hsm_eq, hfs_sm, hphys_sm, hperm_sm⟩ :=
      steps_lift_setTidOnly hc.no_hooks hsvc hHookFree hsteps_st hrun_cm' s0 (initFsState inputs0)
        (congrArg (stripS (progKeep P_rx)) hs0_0_eq)
    have hpc_sm : sm.pc = mpl.base 617 := by
      rw [mpl_base617_eq_cMainAddr_of_linkedAt hls]
      have := congrArg State.pc hsm_eq; simpa [stripS, State.setFs] using this.symm.trans hpc_cm'
    have hrun_sm : sm.status = .Running := by
      have := congrArg State.status hsm_eq
      simpa [stripS, State.setFs] using this.symm.trans hrun_cm'
    have hsp_sm : sm.sp = sl.sp0 - 48#64 := by
      have := congrArg State.sp hsm_eq; simpa [stripS, State.setFs] using this.symm.trans hsp_cm'
    have hal_sm : sm.spAligned = true := by
      simp only [State.spAligned, hsp_sm] at hsp_al_cm' ⊢
      rwa [← hsp_cm']
    have hlr_sm : sm.readReg64 .lr = L.libcStartMainStage2Addr + 56#64 := by
      have : s_cm'.readReg64 .lr = sm.readReg64 .lr := by rw [hsm_eq]; rfl
      exact this.symm.trans hlr_cm'
    have hx0_sm64 : sm.readReg64 .x0 = BitVec.ofNat 64 inputs0.argv.length := by
      have : s_cm'.readReg64 .x0 = sm.readReg64 .x0 := by rw [hsm_eq]; rfl
      exact this.symm.trans hx0_cm'
    have hx0_sm32 : (sm.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 (i.argv.length + 1) := by
      rw [hx0_sm64]
      have hlen_argv : inputs0.argv.length = i.argv.length + 1 := by
        simp [inputs0, f3EmptyFsInputs, cliInputs, processInputs]
      rw [hlen_argv]
      apply BitVec.eq_of_toNat_eq; simp
    have hx1_sm : sm.readReg64 .x1 = sl.argvTableAddr := by
      have : s_cm'.readReg64 .x1 = sm.readReg64 .x1 := by rw [hsm_eq]; rfl
      exact this.symm.trans hx1_cm'
    have htp_sm : sm.tpidrEl0 = L.builtinTlsAddr + 200#64 := by
      have := congrArg State.tpidrEl0 hsm_eq
      simpa [stripS, State.setFs] using this.symm.trans htp_cm'
    have htr_sm : sm.trace = s0.trace := by
      have h1 : s_cm'.trace = sm.trace := by rw [hsm_eq]; rfl
      have h2 : s0'.trace = s0.trace := by simp [s0', stripS, hs0_0_eq, State.setFs]
      exact h1.symm.trans (htlf_cm'.2.1.trans h2)
    have hbrk_sm : sm.brk = L.brkStart := by
      have h1 : s_cm'.brk = sm.brk := by rw [hsm_eq]; rfl
      exact h1.symm.trans (htlf_cm'.2.2.2.1.trans (hinfo'.s0_brk.trans hbrk_eq))
    have hbrkS_sm : sm.brkStart = L.brkStart := by
      have h1 : s_cm'.brkStart = sm.brkStart := by rw [hsm_eq]; rfl
      exact h1.symm.trans (htlf_cm'.2.2.2.2.1.trans (hinfo'.s0_brkStart.trans hbrk_eq))
    have hbrk_s0 : s0.brk = L.brkStart := hbrk0.trans (hinfo0.s0_brk.trans hbrk_eq)
    have hbrkS_s0 : s0.brkStart = L.brkStart := hbrkS0.trans (hinfo0.s0_brkStart.trans hbrk_eq)
    have hvm_sm : StartupVmPreserved s0 sm :=
      ⟨hbrkS_sm.trans hbrkS_s0.symm, hbrk_sm.trans hbrk_s0.symm, hphys_sm, hperm_sm⟩
    have hCO0 : F3CodeOk mpl mmpl s0.mem := f3CodeOk_of_patchedLoadState hls hmng hload
    have hCO_sm : F3CodeOk mpl mmpl sm.mem :=
      f3CodeOk_of_keepsFrozen_and_perm hCO0 hsteps_P.keepsFrozen hperm_sm
    have hm_sm_stripped :
        stripExecOutside (progKeep P_rx) sm.mem ⊨ P_out ∗ R_view := by
      have hmem_eq : s_cm'.mem = stripExecOutside (progKeep P_rx) sm.mem := by rw [hsm_eq]; rfl
      rwa [← hmem_eq]
    have hm_sm_unstripped : sm.mem ⊨ P_out ∗ cliStaticsPlacedAt mpl :=
      hunstrip (fun a => (hperm_sm a).trans (by rw [hmem0])) hm_sm_stripped
    have hm_sm_post := Satisfies.mono (sepConj_mono_left hent_out) hm_sm_unstripped
    let Fr : SepProp :=
      Inst.f3MallocngRoPad ∗ f3StartupResidual L elf i ∗ StdMuslExitGlobalsNoNeedLocks L 0#8
    have hm_sm_entry : sm.mem ⊨
        VerifiedLibraries.mallocngLib.dataInit mmpl ∗
          ((sm.tpidrEl0 - 164#64) ↦₃₂ 0#32) ∗
          (((mallocngAddrsOfPlacement mmpl).libc + 3#64) ↦₈ 0#8) ∗
          (((mallocngAddrsOfPlacement mmpl).libc + 48#64) ↦₆₄ 4096#64) ∗
          (((mallocngAddrsOfPlacement mmpl).libc + 8#64) ↦₆₄ sl.auxvTableAddr) ∗
          MallocngAuxvAt sl.auxvTableAddr ∗
          (LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2.argvAtRO
              (sm.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString) ∗
            stackAt sm.sp cliMainStk ∗ cliStaticsPlacedAt mpl ∗ Fr) := by
      have hargv_eq : inputs0.argv = ("libsignal-cli" :: i.argv).map bytesOfString := rfl
      rw [hlibc_mmpl, htp_sm, hx1_sm, hsp_sm, ← startup_argvAtRO_eq_strict_argvAtRO, ← hargv_eq]
      refine Satisfies.mono ?_ hm_sm_post
      dsimp only [Fr]
      refine Entails.trans
        (Q := (StdExtraRo L ∗ StdExtraRw L) ∗
          (((L.libcAddr + 3#64) ↦₈ 0#8) ∗
            argvAtRO sl.argvTableAddr inputs0.argv ∗
            stackAt (sl.sp0 - 48#64) cliMainStk ∗
            ((L.builtinTlsAddr + 200#64 - 164#64) ↦₃₂ 0#32) ∗
            ((L.libcAddr + 8#64) ↦₆₄ sl.auxvTableAddr) ∗
            ((L.libcAddr + 48#64) ↦₆₄ 4096#64) ∗
            MallocngAuxvAt sl.auxvTableAddr ∗
            f3StartupResidual L elf i ∗
            StdMuslExitGlobalsNoNeedLocks L 0#8 ∗
            cliStaticsPlacedAt mpl))
        (by sep_entail) ?_
      refine Entails.trans
        (sepConj_mono_left (f3StdExtra_entails_mallocngDataInit_of_linkedAt hmng)) ?_
      sep_entail
    refine ⟨s0, sm, Fr, sl.auxvTableAddr, 0#32, hload, hsteps_P, hpc_sm, hrun_sm, hal_sm,
      hfs_sm, htr_sm, hlr_sm, hx0_sm32, hvm_sm,
      htp_sm ▸ lf.tp_bounds.1, htp_sm ▸ lf.tp_bounds.2,
      hCO_sm, hCO_sm.1.mngCode, hsp_sm ▸ hsp_cm' ▸ hsp_ge_cm', hm_sm_entry,
      fun sr hsteps1 hret hm_sr => ?_⟩
    rw [hlibc_mmpl] at hm_sr
    have hL_sr_rx : P_rx.CodeLoaded sr.mem := by
      rw [show P_rx = Tie.f3TrialRxProg from f3PatchedElf_rxProgram_eq]
      exact hCO_sm.1.rxCode.of_keepsFrozen hsteps1.keepsFrozen
    have hm_reord : sr.mem ⊨ ((L.libcAddr + 3#64) ↦₈ 0#8) ∗
        (stackAt sm.sp 80 ∗ StdMuslExitGlobalsNoNeedLocks L 0#8 ∗
          (Inst.f3MallocngRoPad ∗ f3StartupResidual L elf i ∗ anyHeap)) := by
      dsimp only [Fr] at hm_sr
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm_sr
    have hm_frz := Satisfies.of_bupd_frame_left (pointsTo8_freeze_ro (L.libcAddr + 3#64) 0#8) hm_reord
    have hm_exit : sr.mem ⊨ stackAt sm.sp 80 ∗ StdMuslExitGlobals L 0#8 ∗ anyHeap := by
      refine Satisfies.mono ?_ hm_frz
      dsimp only [StdMuslExitGlobalsNoNeedLocks, StdMuslExitGlobals]
      have hany : Inst.f3MallocngRoPad ∗ f3StartupResidual L elf i ∗ anyHeap ⊢ anyHeap :=
        entails_anyHeap _
      refine Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hany))) ?_
      sep_entail
    exact f3Exit80_of_layout lf hc hsvc hHookFree (initFsState inputs0)
      hL_sr_rx hlr_sm hal_sm hret hm_exit
  · exact False.elim (not_satisfies_false_sepConj hfalse)

/-- Unguarded corollary of `cliElf_f3MuslHarnessLr_of_linkedAt` (statement unchanged from `main`). -/
theorem cliElf_f3MuslHarness_of_linkedAt {mpl mmpl : Obj.MultiPlacement}
    (hls : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hmng : VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl) (W : CliHooks) :
    MuslHarnessFineNeedLocksPerInput 80 (mallocngAddrsOfPlacement mmpl).libc
      (patchElfTokensPlacedAt mpl cliElfImage)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (mpl.base 617) cliProcessInputs mmpl
      cliBudgetLimits fineCostModel.init cliMainStk (F3CodeOk mpl mmpl) (cliStaticsPlacedAt mpl) :=
  (cliElf_f3MuslHarnessLr_of_linkedAt hls hmng W).toUnguarded

/-! ## Closed `CliElfF3B2NeedLocksAssumptions` Witness -/

/-- Closed `CliElfF3B2NeedLocksAssumptions` bundle on `cliElfImage` for arbitrary
`LinkedAt cliElfBytes` placements `(mpl, mmpl)`. -/
theorem cliElf_f3B2NeedLocksAssumptions {mpl mmpl : Obj.MultiPlacement}
    (hls : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hmng : VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl) :
    CliElfF3B2NeedLocksAssumptions mpl mmpl 80
      (mallocngAddrsOfPlacement mmpl).libc cliMainStk (F3CodeOk mpl mmpl) cliElfImage where
  elfStaticOk := cliElf_staticOk
  codeMatches := ElfPlaced.cliElf_codeMatchesPlaced_of_linkedAt hls hmng
  tokenCells := cliElf_tokenCellsPlacedAt_of_linkedAt hls
  mallocngLayout := cliElf_f3MallocngLayout
  base547NeZero := ElfCodeMatchesPlaced.f3CliElf_libsignal_base547_ne_zero_of_linkedAt hls
  stkLo := by decide
  stkHi := by decide
  fsEq := fun _ => rfl
  codeLoaded := fun W _ hCO => codeLoaded_cliProgExtPlaced_of_codeRoLoaded W hCO.1.lsRo
  harness := cliElf_f3MuslHarness_of_linkedAt hls hmng

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
