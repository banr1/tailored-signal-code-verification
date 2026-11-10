/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.CliBinaryTokenPatch
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfFrozen
public import LibsignalBinary.Proofs.E2E.Record.Support.ImageWitness
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed
public import LibsignalBinary.Proofs.E2E.HooksE.Common
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.StackBudget
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliBinaryFixed
import LibsignalBinary.Proofs.SignalSession.Cli.Main.MuslHarnessOk
import LibsignalBinary.Proofs.SignalSession.Cli.ProcessBridge

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

/-!
# Whole-Binary CLI Composition

Layout-generic composition from `MainOkCliSm`, `Cli.MuslHarness` / `Cli.muslHarness_ok`, and ELF
`PT_LOAD` segment-slice witnesses (`CliElfFrozen`, `CliElfStatics`, `CliElfTokenCells`, and the
`DEV-CLI10` token patch `patchElfTokens`) to `CliBinaryCorrect elf` and
`LibsignalCliBinaryCorrect bytes`.
-/

namespace CryptoVerification.SignalSession

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession.MuslElf CryptoVerification.SignalSession.ElfFrozen
open CryptoVerification.SignalSession.InitStack

/-! ## 1. Constructive `Obj.Image` of `libsignalSessionImage` at `cliBase` -/

/-- Generalization of `ImageWitness.linkedImage_load_zero_eq_ok` to any page-aligned `base`. -/
theorem linkedImage_load_eq_ok (li : Obj.LinkedImage) (base : BitVec 64)
    (hal : (base.toNat % Obj.pageSize != 0) = false)
    (hwrap : base.toNat + li.gotOff + 8 * li.got.length ≤ 2 ^ 64)
    (hwf : li.wellFormed = true)
    (hrel : li.relocs.all (Record.ImageWitness.DataReloc.okAt base) = true) :
    li.load base = .ok
      { base := base
        code := li.code
        dataAddr := base + BitVec.ofNat 64 li.dataOff
        data := li.relocs.foldl (Record.ImageWitness.DataReloc.applyPure base)
          (li.data ++ List.replicate li.bss 0)
        roData := li.roData.map fun (o, n) => (base + BitVec.ofNat 64 o, n)
        externData := li.externData.map fun (x, o, n) => (x, base + BitVec.ofNat 64 o, n)
        gotAddr := base + BitVec.ofNat 64 li.gotOff
        got := li.got.map (Obj.GotEntry.value base)
        symbols := li.symbols
        objSymbols := li.objSymbols
        stubs := li.stubs } := by
  have hw : ¬ (base.toNat + li.gotOff + 8 * li.got.length > 2 ^ 64) := by omega
  have hwf' : (!li.wellFormed) = false := by simp [hwf]
  simp only [Obj.LinkedImage.load, bind, Except.bind, pure, Except.pure,
    hal, hw, hwf', Bool.false_eq_true, ↓reduceIte,
    Record.ImageWitness.foldlM_dataReloc_eq_ok li.relocs _ hrel]

private theorem cliBase_pageAligned : (cliBase.toNat % Obj.pageSize != 0) = false := rfl

open ProofLib.ProgramReflection in
private theorem cliBase_got_wrap :
    cliBase.toNat + libsignalSessionImage.gotOff + 8 * libsignalSessionImage.got.length ≤ 2 ^ 64 :=
  Nat.le_of_ble_eq_true (by rfl_kernel)

open ProofLib.ProgramReflection in
private theorem cliBase_relocs_ok :
    libsignalSessionImage.relocs.all (Record.ImageWitness.DataReloc.okAt cliBase) = true := by
  rfl_kernel

/-- Canonical `Obj.Image` obtained by loading `libsignalSessionImage` at `cliBase`.
Marked `@[irreducible]` after proving `loads_cliImg` and `cliImg_base` so downstream elaboration
never unfolds the relocation fold over `libsignalSessionImage.data`. -/
noncomputable def cliImg : Obj.Image :=
  { base := cliBase
    code := libsignalSessionImage.code
    dataAddr := cliBase + BitVec.ofNat 64 libsignalSessionImage.dataOff
    data := libsignalSessionImage.relocs.foldl (Record.ImageWitness.DataReloc.applyPure cliBase)
      (libsignalSessionImage.data ++ List.replicate libsignalSessionImage.bss 0)
    roData := libsignalSessionImage.roData.map fun (o, n) => (cliBase + BitVec.ofNat 64 o, n)
    externData := libsignalSessionImage.externData.map fun (x, o, n) =>
      (x, cliBase + BitVec.ofNat 64 o, n)
    gotAddr := cliBase + BitVec.ofNat 64 libsignalSessionImage.gotOff
    got := libsignalSessionImage.got.map (Obj.GotEntry.value cliBase)
    symbols := libsignalSessionImage.symbols
    objSymbols := libsignalSessionImage.objSymbols
    stubs := libsignalSessionImage.stubs }

/-- `cliImg` has load base `cliBase`. -/
theorem cliImg_base : cliImg.base = cliBase := rfl

/-- `libsignalSessionImage` loads cleanly at `cliBase` to `cliImg`. -/
theorem loads_cliImg : Obj.Loads libsignalSessionImage cliImg := by
  unfold Obj.Loads
  rw [cliImg_base]
  exact linkedImage_load_eq_ok libsignalSessionImage cliBase cliBase_pageAligned cliBase_got_wrap
    Record.ImageWitness.libsignalSessionImage_wellFormed' cliBase_relocs_ok

attribute [irreducible] cliImg

/-- Code length of `cliImg` equals `libsignalSessionImage.code.length` (without unfolding `cliImg`). -/
theorem cliImg_code_length : cliImg.code.length = libsignalSessionImage.code.length := by
  rw [(ProofLib.ObjectLoad.Loads.canonical loads_cliImg).1]

/-! ## 2. `CliElfCodeMatches` and `FrozenLoaded` from ELF `SegSlice`s -/

/-- General `CliElfCodeMatches` bridge: if `elf` maps a `Perm.rx` byte slice `codeBytes` at
`cliBase` that agrees with `libsignalSessionImage.toProgram.code` outside the 5 branch stubs
`InCliBranchStub`, then `CliElfCodeMatches elf` holds. -/
theorem cliElfCodeMatches_of_patchedSlice {elf : ElfImage} {codeBytes : List (BitVec 8)}
    (hE : Cli.ElfStaticOk elf)
    (hslice : SegSlice elf cliBase codeBytes Perm.rx)
    (hlen : codeBytes.length = libsignalSessionImage.toProgram.code.length)
    (heq : ∀ (k : Nat) (hk : k < codeBytes.length),
      ¬ InCliBranchStub k →
        codeBytes[k] = libsignalSessionImage.toProgram.code[k]'(hlen ▸ hk)) :
    CliElfCodeMatches elf := by
  intro i s0 hload k hk
  have hk' : k < codeBytes.length := hlen.symm ▸ hk
  have hh := (hslice.holdsBytes hE.1 hE.2 hload) k hk'
  exact ⟨hh.2.1, fun hnot => hh.1.trans (heq k hk' hnot)⟩

/-- When `elf` maps `libsignalSessionImage.code` verbatim at `cliBase` as `Perm.rx`,
`CliElfCodeMatches elf` holds directly. -/
theorem cliElfCodeMatches_of_codeSlice {elf : ElfImage}
    (hE : Cli.ElfStaticOk elf)
    (hcode : SegSlice elf cliBase libsignalSessionImage.code Perm.rx) :
    CliElfCodeMatches elf :=
  cliElfCodeMatches_of_patchedSlice hE hcode rfl (fun _ _ _ => rfl)

/-- Bundle of `PT_LOAD` segment slices witnessing `img.FrozenLoaded` after `elf.loadState`
without evaluating the relocation fold in the kernel (`ElfFrozen.frozenLoaded_of_loads_pieces`). -/
structure CliElfFrozen (elf : ElfImage) (img : Obj.Image) : Prop where
  code : SegSlice elf img.base libsignalSessionImage.code Perm.rx
  data_len : libsignalSessionImage.data.length + libsignalSessionImage.bss < 2 ^ 64
  ro_runs : ∃ runs : List (Nat × List Piece),
    (∀ r ∈ runs,
      r.1 + piecesLen r.2 ≤ libsignalSessionImage.data.length + libsignalSessionImage.bss ∧
      piecesOk libsignalSessionImage.relocs
        (libsignalSessionImage.data.length + libsignalSessionImage.bss) r.1 r.2 = true ∧
      SegSlice elf (img.base + BitVec.ofNat 64 libsignalSessionImage.dataOff + BitVec.ofNat 64 r.1)
        (piecesBytes img.base
          ((libsignalSessionImage.data ++ List.replicate libsignalSessionImage.bss 0).drop r.1) r.2)
        Perm.ro) ∧
    (∀ q ∈ libsignalSessionImage.roData,
      libsignalSessionImage.dataOff ≤ q.1 ∧
      ∃ r ∈ runs, r.1 ≤ q.1 - libsignalSessionImage.dataOff ∧
        q.1 - libsignalSessionImage.dataOff + q.2 ≤ r.1 + piecesLen r.2)
  got : SegSlice elf (img.base + BitVec.ofNat 64 libsignalSessionImage.gotOff)
    ((libsignalSessionImage.got.map (Obj.GotEntry.value img.base)).flatMap (Obj.bytesLE 8)) Perm.ro

/-- `CliElfFrozen` discharges `MuslHarnessOk`'s `hF` obligation for any loaded image of
`libsignalSessionImage`. -/
theorem CliElfFrozen.frozenLoaded {elf : ElfImage} {img : Obj.Image}
    (hfz : CliElfFrozen elf img) (himg : Obj.Loads libsignalSessionImage img)
    (hE : Cli.ElfStaticOk elf) :
    ∀ i s0, elf.loadState (Cli.cliInputs i) = .ok s0 → img.FrozenLoaded s0 := by
  intro _ _ hload
  obtain ⟨runs, hruns_ok, hro_cover⟩ := hfz.ro_runs
  exact frozenLoaded_of_loads_pieces himg runs hE.1 hE.2 hfz.code hfz.data_len hruns_ok
    hro_cover hfz.got hload

/-- At `img.base = cliBase`, `CliElfFrozen.code` also yields `CliElfCodeMatches elf`. -/
theorem CliElfFrozen.codeMatches {elf : ElfImage} {img : Obj.Image}
    (hfz : CliElfFrozen elf img) (hbase : img.base = cliBase) (hE : Cli.ElfStaticOk elf) :
    CliElfCodeMatches elf := by
  have hcode : SegSlice elf cliBase libsignalSessionImage.code Perm.rx := hbase ▸ hfz.code
  exact cliElfCodeMatches_of_codeSlice hE hcode

/-! ## 3. Writable CLI statics (`E2E.HooksE.A0.pool ∗ Cli.cliStatics img`) from `SegSlice`s -/

/-- Disjointness of two half-open byte intervals `[r1.1, r1.1 + r1.2)` and `[r2.1, r2.1 + r2.2)`. -/
def ByteRangeDisjoint (r1 r2 : Nat × Nat) : Prop :=
  r1.1 + r1.2 ≤ r2.1 ∨ r2.1 + r2.2 ≤ r1.1

instance instDecidableByteRangeDisjoint (r1 r2 : Nat × Nat) :
    Decidable (ByteRangeDisjoint r1 r2) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Pairwise disjointness of a list of half-open byte intervals. -/
def ByteRangesDisjoint : List (Nat × Nat) → Prop
  | [] => True
  | r :: rs => (∀ q ∈ rs, ByteRangeDisjoint r q) ∧ ByteRangesDisjoint rs

instance instDecidableByteRangesDisjoint : (rs : List (Nat × Nat)) →
    Decidable (ByteRangesDisjoint rs)
  | [] => isTrue trivial
  | _ :: rs =>
    haveI := instDecidableByteRangesDisjoint rs
    inferInstanceAs (Decidable (_ ∧ _))

def inRange (r : Nat × Nat) (k : Nat) : Prop :=
  r.1 ≤ k ∧ k < r.1 + r.2

private theorem inRange_disjoint {r1 r2 : Nat × Nat} (hd : ByteRangeDisjoint r1 r2)
    {k : Nat} (h1 : inRange r1 k) (h2 : inRange r2 k) : False := by
  unfold ByteRangeDisjoint at hd
  unfold inRange at h1 h2
  omega

/-- The five writable static byte ranges owned by `Cli.cliStatics img`:
`coins::NEXT.0` (8B), `coins::LEFT.0` (8B), `TOKEN` `STORAGE.0` (1B), `TOKEN` `Once` state (4B),
and `log::MAX_LOG_LEVEL_FILTER` (8B). -/
def cliStaticsRanges (img : Obj.Image) : List (Nat × Nat) :=
  [ ((img.base + Cli.coinsNextOff).toNat, 8),
    ((img.base + Cli.coinsLeftOff).toNat, 8),
    ((CryptoVerification.LibsignalSpqrV1.tokenStorageAddr img).toNat, 1),
    ((CryptoVerification.LibsignalSpqrV1.tokenOnceAddr img).toNat, 4),
    ((CryptoVerification.LibsignalSession.logFilterAddr img).toNat, 8) ]

/-- Footprint predicate `S : Nat → Prop` for `Cli.cliStatics img`. -/
def CliStaticsFootprint (img : Obj.Image) (k : Nat) : Prop :=
  inRange ((img.base + Cli.coinsNextOff).toNat, 8) k ∨
  inRange ((img.base + Cli.coinsLeftOff).toNat, 8) k ∨
  inRange ((CryptoVerification.LibsignalSpqrV1.tokenStorageAddr img).toNat, 1) k ∨
  inRange ((CryptoVerification.LibsignalSpqrV1.tokenOnceAddr img).toNat, 4) k ∨
  inRange ((CryptoVerification.LibsignalSession.logFilterAddr img).toNat, 8) k

/-- Start of musl's 600-byte writable static block (`elf.entry + 2 * Obj.pageSize`). -/
abbrev muslRwStart (elf : ElfImage) : BitVec 64 :=
  HAdd.hAdd elf.entry (BitVec.ofNat 64 (2 * Obj.pageSize))

/-- Proof-side bundle of `Perm.rw` `PT_LOAD` segment slices witnessing `Cli.cliStatics img` at
`elf.loadState`, disjoint from musl's 600-byte writable static block at `muslRwStart elf`. -/
structure CliElfStatics (elf : ElfImage) (img : Obj.Image) : Prop where
  coinsNext : ∃ v : BitVec 64, SegSlice elf (img.base + Cli.coinsNextOff) (unpack64 v) Perm.rw
  coinsLeft : ∃ v : BitVec 64, SegSlice elf (img.base + Cli.coinsLeftOff) (unpack64 v) Perm.rw
  tokenStorage :
    SegSlice elf (CryptoVerification.LibsignalSpqrV1.tokenStorageAddr img) [0#8] Perm.rw
  tokenOnce :
    SegSlice elf (CryptoVerification.LibsignalSpqrV1.tokenOnceAddr img) [0#8, 0#8, 0#8, 0#8] Perm.rw
  logFilter :
    SegSlice elf (CryptoVerification.LibsignalSession.logFilterAddr img)
      (List.replicate 8 0#8) Perm.rw
  disjoint :
    ByteRangesDisjoint (((muslRwStart elf).toNat, 600) :: cliStaticsRanges img)

private theorem segSlice_supportedOn_rw {elf : ElfImage} {a : BitVec 64} {bs : List (BitVec 8)}
    (hs : SegSlice elf a bs Perm.rw) (hne : bs ≠ []) (hE : Cli.ElfStaticOk elf)
    {inputs : ProcessInputs} {s0 : State} (hload : elf.loadState inputs = .ok s0) :
    SupportedOn 0#64 (inRange (a.toNat, bs.length)) s0.mem (a ↦ₛ bs) := by
  have hb := hs.bound hne hE.1 hE.2
  have hsb := stackBase_eq
  exact supportedOn_of_holdsBytes_rw (by omega) (hs.holdsBytes hE.1 hE.2 hload)

private theorem supportedOn_coins64 {elf : ElfImage} {a : BitVec 64}
    (hex : ∃ v : BitVec 64, SegSlice elf a (unpack64 v) Perm.rw)
    (hE : Cli.ElfStaticOk elf) {inputs : ProcessInputs} {s0 : State}
    (hload : elf.loadState inputs = .ok s0) :
    SupportedOn 0#64 (inRange (a.toNat, 8)) s0.mem (∃∗ v : BitVec 64, a ↦₆₄ v) := by
  obtain ⟨v, hs⟩ := hex
  have hlen : (unpack64 v).length = 8 := by simp [unpack64]
  have hne : unpack64 v ≠ [] := by intro hc; rw [hc] at hlen; cases hlen
  have hsup := segSlice_supportedOn_rw hs hne hE hload
  rw [hlen, ← ProofLib.pointsTo64_eq_pointsToBytes a v] at hsup
  exact hsup.mono (Entails.sepExists_right v (Entails.refl _))

/-- `CliElfStatics` discharges `MuslHarnessOk`'s `hR` support obligation for
`E2E.HooksE.A0.pool ∗ Cli.cliStatics img` on every loaded state. -/
theorem CliElfStatics.supportedOn_pool_cliStatics {elf : ElfImage} {img : Obj.Image}
    (hst : CliElfStatics elf img) (hE : Cli.ElfStaticOk elf) :
    ∀ i s0, elf.loadState (Cli.cliInputs i) = .ok s0 →
      SupportedOn 0#64 (CliStaticsFootprint img) s0.mem
        (HooksE.A0.pool ∗ Cli.cliStatics img) := by
  intro i s0 hload
  obtain ⟨_, ⟨hd1, hd2, hd3, hd4, hd5, _⟩⟩ := hst.disjoint
  have s1 := supportedOn_coins64 hst.coinsNext hE hload
  have s2 := supportedOn_coins64 hst.coinsLeft hE hload
  have s3 := segSlice_supportedOn_rw hst.tokenStorage (by simp) hE hload
  simp only [List.length_singleton, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp] at s3
  have s4 := segSlice_supportedOn_rw hst.tokenOnce (by simp) hE hload
  have hp32 : (CryptoVerification.LibsignalSpqrV1.tokenOnceAddr img ↦₃₂ 0#32) =
      (CryptoVerification.LibsignalSpqrV1.tokenOnceAddr img ↦ₛ [0#8, 0#8, 0#8, 0#8]) := by
    rw [ProofLib.pointsTo32_eq_pointsToBytes]; rfl
  change SupportedOn 0#64 (inRange ((CryptoVerification.LibsignalSpqrV1.tokenOnceAddr img).toNat, 4))
    s0.mem _ at s4
  rw [← hp32] at s4
  have s5 := segSlice_supportedOn_rw hst.logFilter (by simp) hE hload
  have hlog : (CryptoVerification.LibsignalSession.logFilterAddr img ↦ₛ List.replicate 8 0#8) =
      CryptoVerification.LibsignalTripleRatchet.logOff img := by
    unfold CryptoVerification.LibsignalTripleRatchet.logOff
    rw [ProofLib.pointsTo64_eq_pointsToBytes]; rfl
  rw [List.length_replicate, hlog] at s5
  have s12 := s1.sepConj s2 (fun k h1 h2 =>
    inRange_disjoint (hd1 _ (by simp)) h1 h2)
  have s34 := s3.sepConj s4 (fun k h3 h4 =>
    inRange_disjoint (hd3 _ (by simp)) h3 h4)
  have s345 := s34.sepConj s5 (fun k h34 h5 => by
    rcases h34 with h3 | h4
    · exact inRange_disjoint (hd3 _ (by simp)) h3 h5
    · exact inRange_disjoint (hd4 _ (by simp)) h4 h5)
  have sAll := s12.sepConj s345 (fun k h12 h345 => by
    rcases h12 with h1 | h2 <;> rcases h345 with (h3 | h4) | h5
    · exact inRange_disjoint (hd1 _ (by simp)) h1 h3
    · exact inRange_disjoint (hd1 _ (by simp)) h1 h4
    · exact inRange_disjoint (hd1 _ (by simp)) h1 h5
    · exact inRange_disjoint (hd2 _ (by simp)) h2 h3
    · exact inRange_disjoint (hd2 _ (by simp)) h2 h4
    · exact inRange_disjoint (hd2 _ (by simp)) h2 h5)
  have hprop : (HooksE.A0.pool ∗ Cli.cliStatics img) =
      (((∃∗ v : BitVec 64, (img.base + Cli.coinsNextOff) ↦₆₄ v) ∗
        (∃∗ v : BitVec 64, (img.base + Cli.coinsLeftOff) ↦₆₄ v)) ∗
       (((CryptoVerification.LibsignalSpqrV1.tokenStorageAddr img ↦₈ 0#8) ∗
         (CryptoVerification.LibsignalSpqrV1.tokenOnceAddr img ↦₃₂ 0#32)) ∗
        CryptoVerification.LibsignalTripleRatchet.logOff img)) := by
    change (emp ∗ Cli.cliStatics img) = _
    rw [emp_sepConj]
    unfold Cli.cliStatics Cli.coinsStatics CryptoVerification.LibsignalSpqrV1.TokenInit
    ac_rfl
  rw [← hprop] at sAll
  exact sAll.widen (fun k hk => by
    unfold CliStaticsFootprint
    rcases hk with (h1 | h2) | ((h3 | h4) | h5)
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h5))))

/-- Generalizes `CliElfStatics.supportedOn_pool_cliStatics` from `HooksE.A0` to any
`A : RustHeap.RustAlloc` whose pool holds on the empty heap (`emp ⊢ A.pool`). -/
theorem CliElfStatics.supportedOn_pool_cliStatics_pool {elf : ElfImage} {img : Obj.Image}
    {A : RustHeap.RustAlloc} (hst : CliElfStatics elf img) (hpool : emp ⊢ A.pool)
    (hE : Cli.ElfStaticOk elf) :
    ∀ i s0, elf.loadState (Cli.cliInputs i) = .ok s0 →
      SupportedOn 0#64 (CliStaticsFootprint img) s0.mem
        (A.pool ∗ Cli.cliStatics img) := by
  intro i s0 hload
  exact (hst.supportedOn_pool_cliStatics hE i s0 hload).mono (sepConj_mono_left hpool)

/-- `CliExternsOk` specialization of `CliElfStatics.supportedOn_pool_cliStatics_pool` via
`hOk.poolEmp : emp ⊢ A.pool`. -/
theorem CliElfStatics.supportedOn_pool_cliStatics_ext {elf : ElfImage} {img : Obj.Image}
    {P : PEParams} {A : RustHeap.RustAlloc} {ext : String → Option (State → State)}
    (hst : CliElfStatics elf img) (hOk : CliExternsOk P A ext)
    (hE : Cli.ElfStaticOk elf) :
    ∀ i s0, elf.loadState (Cli.cliInputs i) = .ok s0 →
      SupportedOn 0#64 (CliStaticsFootprint img) s0.mem
        (A.pool ∗ Cli.cliStatics img) :=
  hst.supportedOn_pool_cliStatics_pool hOk.poolEmp hE

/-- `CliElfStatics` discharges `MuslHarnessOk`'s `hS` footprint bound obligation. -/
theorem CliElfStatics.footprint_bounds {elf : ElfImage} {img : Obj.Image}
    (hst : CliElfStatics elf img) (hE : Cli.ElfStaticOk elf) :
    ∀ k, CliStaticsFootprint img k → k < stackBase ∧
      ¬((muslRwStart elf).toNat ≤ k ∧ k < (muslRwStart elf).toNat + 600) := by
  intro k hk
  obtain ⟨hdMusl, _⟩ := hst.disjoint
  obtain ⟨v1, hs1⟩ := hst.coinsNext
  obtain ⟨v2, hs2⟩ := hst.coinsLeft
  have hb1 : (img.base + Cli.coinsNextOff).toNat + 8 ≤ stackBase := by
    have h := hs1.bound (by simp [unpack64]) hE.1 hE.2
    simpa [unpack64] using h
  have hb2 : (img.base + Cli.coinsLeftOff).toNat + 8 ≤ stackBase := by
    have h := hs2.bound (by simp [unpack64]) hE.1 hE.2
    simpa [unpack64] using h
  have hb3 : (CryptoVerification.LibsignalSpqrV1.tokenStorageAddr img).toNat + 1 ≤ stackBase :=
    hst.tokenStorage.bound (by simp) hE.1 hE.2
  have hb4 : (CryptoVerification.LibsignalSpqrV1.tokenOnceAddr img).toNat + 4 ≤ stackBase :=
    hst.tokenOnce.bound (by simp) hE.1 hE.2
  have hb5 : (CryptoVerification.LibsignalSession.logFilterAddr img).toNat + 8 ≤ stackBase := by
    have h := hst.logFilter.bound (by simp) hE.1 hE.2
    simpa using h
  rcases hk with h1 | h2 | h3 | h4 | h5
  · exact ⟨by unfold inRange at h1; omega,
      fun hm => inRange_disjoint (hdMusl _ (by simp [cliStaticsRanges])) hm h1⟩
  · exact ⟨by unfold inRange at h2; omega,
      fun hm => inRange_disjoint (hdMusl _ (by simp [cliStaticsRanges])) hm h2⟩
  · exact ⟨by unfold inRange at h3; omega,
      fun hm => inRange_disjoint (hdMusl _ (by simp [cliStaticsRanges])) hm h3⟩
  · exact ⟨by unfold inRange at h4; omega,
      fun hm => inRange_disjoint (hdMusl _ (by simp [cliStaticsRanges])) hm h4⟩
  · exact ⟨by unfold inRange at h5; omega,
      fun hm => inRange_disjoint (hdMusl _ (by simp [cliStaticsRanges])) hm h5⟩

/-! ## 3b. Lifting `CliElfFrozen` and `CliElfMusl` across `patchElfTokens` (`DEV-CLI10`) -/

/-- `CliElfFrozen elf cliImg` on the unpatched ELF lifts directly to `(patchElfTokens elf).loadState`
with zero stub or `.data` exceptions. -/
theorem CliElfFrozen.frozenLoaded_patchElfTokens {elf : ElfImage}
    (hfz : CliElfFrozen elf cliImg) (hE : Cli.ElfStaticOk elf) (htok : CliElfTokenCells elf) :
    ∀ i s0', (patchElfTokens elf).loadState (Cli.cliInputs i) = .ok s0' →
      cliImg.FrozenLoaded s0' := by
  intro i s0' hload'
  rw [loadState_patchElfTokens hE htok] at hload'
  cases hload : elf.loadState (Cli.cliInputs i) with
  | error _ => rw [hload] at hload'; cases hload'
  | ok s0 =>
    rw [hload] at hload'
    simp only [Except.map, Except.ok.injEq] at hload'
    subst hload'
    exact (hfz.frozenLoaded loads_cliImg hE i s0 hload).of_keepsFrozen
      (keepsFrozen_cliTokenPatch hE htok hload)

private theorem toNat_add_ofNat_lt {x : BitVec 64} {n : Nat} (h : x.toNat + n < 2 ^ 64) :
    (x + BitVec.ofNat 64 n).toNat = x.toNat + n := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]

/-- Lift `CliElfMusl elf code` on the unpatched ELF to `CliElfMusl (patchElfTokens elf) code`. -/
theorem cliElfMusl_patchTokens {elf : ElfImage} {code : List (BitVec 8)}
    (hM : CliElfMusl elf code) (hE : Cli.ElfStaticOk elf) (htok : CliElfTokenCells elf)
    (hdisj : ByteRangesDisjoint (((muslRwStart elf).toNat, 600) :: cliStaticsRanges cliImg)) :
    CliElfMusl (patchElfTokens elf) code := by
  have ro : ∀ {a bs}, SegSlice elf a bs .ro → SegSlice (patchElfTokens elf) a bs .ro :=
    fun h => segSlice_patchElfTokens_of_ne_rw h (by decide) hE htok
  obtain ⟨h0, g3, g4, ia, F, hh0, hrw⟩ := hM.rw
  have hML : (unpackL (muslRwWords h0 g3 g4 ia F)).length = 600 := by rw [unpackL_length]; rfl
  have hne_nil : unpackL (muslRwWords h0 g3 g4 ia F) ≠ [] := by intro hc; rw [hc] at hML; cases hML
  have hMb : (muslRwStart elf).toNat + 600 ≤ stackBase := by
    have hb := hrw.bound hne_nil hE.1 hE.2
    change (muslRwStart elf).toNat + (unpackL (muslRwWords h0 g3 g4 ia F)).length ≤ stackBase at hb
    rwa [hML] at hb
  have hsb := stackBase_eq
  have hs_bnd := htok.storage.bound (by simp) hE.1 hE.2
  have ho_bnd := htok.once.bound (by simp) hE.1 hE.2
  have hd_s : ByteRangeDisjoint ((muslRwStart elf).toNat, 600)
      ((cliBase + CryptoVerification.LibsignalSpqrV1.tokenStorageOff).toNat, 1) := by
    have hmem_s : ((CryptoVerification.LibsignalSpqrV1.tokenStorageAddr cliImg).toNat, 1) ∈
        cliStaticsRanges cliImg := List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
    have h := hdisj.1 _ hmem_s
    rwa [CryptoVerification.LibsignalSpqrV1.tokenStorageAddr, cliImg_base] at h
  have hd_o : ByteRangeDisjoint ((muslRwStart elf).toNat, 600)
      ((cliBase + CryptoVerification.LibsignalSpqrV1.tokenOnceOff).toNat, 4) := by
    have hmem_o : ((CryptoVerification.LibsignalSpqrV1.tokenOnceAddr cliImg).toNat, 4) ∈
        cliStaticsRanges cliImg :=
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    have h := hdisj.1 _ hmem_o
    rwa [CryptoVerification.LibsignalSpqrV1.tokenOnceAddr, cliImg_base] at h
  have hs_ne : ∀ j (_ : j < (unpackL (muslRwWords h0 g3 g4 ia F)).length),
      muslRwStart elf + BitVec.ofNat 64 j ≠
        cliBase + CryptoVerification.LibsignalSpqrV1.tokenStorageOff := by
    intro j hj heq
    rw [hML] at hj
    simp only [List.length_singleton] at hs_bnd
    have htn : (muslRwStart elf).toNat + j =
        (cliBase + CryptoVerification.LibsignalSpqrV1.tokenStorageOff).toNat := by
      rw [← toNat_add_ofNat_lt (x := muslRwStart elf) (n := j) (by omega), heq]
    exact inRange_disjoint hd_s (k := (muslRwStart elf).toNat + j)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  have ho_ne : ∀ d (_ : d < 4) j (_ : j < (unpackL (muslRwWords h0 g3 g4 ia F)).length),
      muslRwStart elf + BitVec.ofNat 64 j ≠
        cliBase + CryptoVerification.LibsignalSpqrV1.tokenOnceOff + BitVec.ofNat 64 d := by
    intro d hd j hj heq
    rw [hML] at hj
    simp only [List.length_cons, List.length_nil] at ho_bnd
    have htn : (muslRwStart elf).toNat + j =
        (cliBase + CryptoVerification.LibsignalSpqrV1.tokenOnceOff).toNat + d := by
      rw [← toNat_add_ofNat_lt (x := muslRwStart elf) (n := j) (by omega), heq,
        toNat_add_ofNat_lt (x := cliBase + CryptoVerification.LibsignalSpqrV1.tokenOnceOff)
          (n := d) (by omega)]
    exact inRange_disjoint hd_o (k := (muslRwStart elf).toNat + j)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  have hrw_s : SegSlice elf (muslRwStart elf) (unpackL (muslRwWords h0 g3 g4 ia F)) .rw := hrw
  have hrw' : SegSlice (patchElfTokens elf) (muslRwStart elf)
      (unpackL (muslRwWords h0 g3 g4 ia F)) .rw :=
    segSlice_patchElfTokens_of_ne hrw_s hE hs_ne
      (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using ho_ne 0 (by omega))
      (ho_ne 1 (by omega)) (ho_ne 2 (by omega)) (ho_ne 3 (by omega))
  exact
    { entry_page := hM.entry_page
      text := segSlice_patchElfTokens_of_ne_rw hM.text (by decide) hE htok
      phnum := hM.phnum
      phdrs :=
        { p0_type := ro hM.phdrs.p0_type, p0_vaddr := ro hM.phdrs.p0_vaddr
          p1_type := ro hM.phdrs.p1_type, p2_type := ro hM.phdrs.p2_type
          p3_type := ro hM.phdrs.p3_type, p4_type := ro hM.phdrs.p4_type
          p5_type := ro hM.phdrs.p5_type, p6_type := ro hM.phdrs.p6_type
          p7_type := ro hM.phdrs.p7_type, p8_type := ro hM.phdrs.p8_type
          p9_type := ro hM.phdrs.p9_type, p9_vaddr := ro hM.phdrs.p9_vaddr
          p9_filesz := ro hM.phdrs.p9_filesz, p9_memsz := ro hM.phdrs.p9_memsz
          p9_align := ro hM.phdrs.p9_align, p10_type := ro hM.phdrs.p10_type
          p10_memsz := ro hM.phdrs.p10_memsz }
      phdr_ne := hM.phdr_ne
      rw := ⟨h0, g3, g4, ia, F, hh0, hrw'⟩ }

/-! ## 4. `MainOkCliSm`, `MuslHarness`, and Whole-Binary / Bytes-Generic Composition -/

/-- `main`-level SM-domain functional specification at `HooksE.A0`, matching the `hmain`
premise of `ProcessBridge.cliBinaryCorrect_of_parts_observe`. -/
def MainOkCliSm (img : Obj.Image) : Prop :=
  ∀ W : CliHooks, ∃ Run : Inputs → Cli.RunAnswer → Prop,
    subroutine_ok (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName)
      (Cli.mainSpec HooksE.A0 img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run) ∧
    (∀ g m, Reach (spqrOffSessionParams W.C) g → m.length < 2 ^ 32 →
      ∃ a, Run (smSendInputs g m) a ∧
        observe (smSendInputs g m).files a =
          observe (smSendInputs g m).files (smSendModel W.C g m) ∧
        Cli.CommitOk (smSendInputs g m) (Cli.MainResult.ofAnswer a)) ∧
    (∀ g c rc, Reach (spqrOffSessionParams W.C) g → c.length < 2 ^ 32 →
      ∃ a, Run (smRecvInputs g c rc) a ∧
        observe (smRecvInputs g c rc).files a =
          observe (smRecvInputs g c rc).files (smRecvModel W.C g c rc) ∧
        Cli.CommitOk (smRecvInputs g c rc) (Cli.MainResult.ofAnswer a))

/-- `cliMainStk` fits within musl startup's `cliStackBudget` (`8,371,792 ≤ 8,371,792`). -/
theorem cliMainStk_le_stackBudget : Cli.MainHops.cliMainStk ≤ cliStackBudget := by
  have := cliStackSize_eq; unfold Cli.MainHops.cliMainStk cliStackBudget cliArgBudget; omega

/-- Byte distance from `elf.entry` (`_start`) down to `main` in `Cli.muslHarness_ok` (`85732` on
the CLI ELF: `0x49c000 - 0x487200 = 0x14ee4`). -/
abbrev muslMainDelta : BitVec 64 := 85504#64

/-- Assemble `Cli.MuslHarness (patchElfTokens elf)` at `cliImg` and `HooksE.A0` from unpatched
`CliElfMusl elf`, unpatched `CliElfFrozen elf cliImg`, `CliElfTokenCells elf`, and
`CliElfStatics (patchElfTokens elf) cliImg`. -/
theorem muslHarness_cliImg_of_elf {elf : ElfImage} {muslCode : List (BitVec 8)}
    (hE : Cli.ElfStaticOk elf)
    (htok : CliElfTokenCells elf)
    (hMusl : CliElfMusl elf muslCode)
    (hend : cliBase.toNat + libsignalSessionImage.code.length ≤ elf.entry.toNat)
    (hfS : MuslStart.MuslStartFetch ({ code := muslCode } : Program) 0#64)
    (hfE : MuslExit.MuslExitFetch ({ code := muslCode } : Program) 0#64)
    (hmainOff : entryOf cliImg Cli.mainName = elf.entry - muslMainDelta)
    (hfz : CliElfFrozen elf cliImg)
    (hstat : CliElfStatics (patchElfTokens elf) cliImg)
    (W : CliHooks) :
    Cli.MuslHarness (patchElfTokens elf) (Cli.cliProg cliImg (cliExterns W))
      (entryOf cliImg Cli.mainName) (MuslExit.muslFiniFr elf.entry)
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre cliImg HooksE.A0 Cli.MainHops.cliMainStk (Cli.cliStatics cliImg)) := by
  have hE' := elfStaticOk_patchElfTokens hE
  have hend' : cliImg.base.toNat + cliImg.code.length ≤ (patchElfTokens elf).entry.toNat := by
    change cliImg.base.toNat + cliImg.code.length ≤ elf.entry.toNat
    rwa [cliImg_base, cliImg_code_length]
  exact Cli.muslHarness_ok loads_cliImg (cliExterns W)
    (cliElfMusl_patchTokens hMusl hE htok hstat.disjoint)
    hend' hfS hfE hmainOff cliMainStk_le_stackBudget
    (hfz.frozenLoaded_patchElfTokens hE htok)
    (hstat.supportedOn_pool_cliStatics hE') (hstat.footprint_bounds hE')

/-- Assemble `Cli.MuslHarness (patchElfTokens elf)` at `cliImg` for any `(A, ext)` satisfying
`emp ⊢ A.pool`. -/
theorem muslHarness_cliImg_of_elf_pool {elf : ElfImage} {muslCode : List (BitVec 8)}
    (hE : Cli.ElfStaticOk elf)
    (htok : CliElfTokenCells elf)
    (hMusl : CliElfMusl elf muslCode)
    (hend : cliBase.toNat + libsignalSessionImage.code.length ≤ elf.entry.toNat)
    (hfS : MuslStart.MuslStartFetch ({ code := muslCode } : Program) 0#64)
    (hfE : MuslExit.MuslExitFetch ({ code := muslCode } : Program) 0#64)
    (hmainOff : entryOf cliImg Cli.mainName = elf.entry - muslMainDelta)
    (hfz : CliElfFrozen elf cliImg)
    (hstat : CliElfStatics (patchElfTokens elf) cliImg)
    {A : RustHeap.RustAlloc} (hpool : emp ⊢ A.pool)
    (ext : String → Option (State → State)) :
    Cli.MuslHarness (patchElfTokens elf) (Cli.cliProg cliImg ext)
      (entryOf cliImg Cli.mainName) (MuslExit.muslFiniFr elf.entry)
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre cliImg A Cli.MainHops.cliMainStk (Cli.cliStatics cliImg)) := by
  have hE' := elfStaticOk_patchElfTokens hE
  have hend' : cliImg.base.toNat + cliImg.code.length ≤ (patchElfTokens elf).entry.toNat := by
    change cliImg.base.toNat + cliImg.code.length ≤ elf.entry.toNat
    rwa [cliImg_base, cliImg_code_length]
  exact Cli.muslHarness_ok loads_cliImg ext
    (cliElfMusl_patchTokens hMusl hE htok hstat.disjoint)
    hend' hfS hfE hmainOff cliMainStk_le_stackBudget
    (hfz.frozenLoaded_patchElfTokens hE htok)
    (hstat.supportedOn_pool_cliStatics_pool hpool hE') (hstat.footprint_bounds hE')

/-- Assemble `Cli.MuslHarness (patchElfTokens elf)` at `cliImg` and `(A, cliExternsWith ext)` from
`CliExternsOk P A ext`. -/
theorem muslHarness_cliImg_of_elf_ext {elf : ElfImage} {muslCode : List (BitVec 8)}
    {P : PEParams} {A : RustHeap.RustAlloc} {ext : String → Option (State → State)}
    (hE : Cli.ElfStaticOk elf)
    (htok : CliElfTokenCells elf)
    (hMusl : CliElfMusl elf muslCode)
    (hend : cliBase.toNat + libsignalSessionImage.code.length ≤ elf.entry.toNat)
    (hfS : MuslStart.MuslStartFetch ({ code := muslCode } : Program) 0#64)
    (hfE : MuslExit.MuslExitFetch ({ code := muslCode } : Program) 0#64)
    (hmainOff : entryOf cliImg Cli.mainName = elf.entry - muslMainDelta)
    (hfz : CliElfFrozen elf cliImg)
    (hstat : CliElfStatics (patchElfTokens elf) cliImg)
    (hOk : CliExternsOk P A ext) :
    Cli.MuslHarness (patchElfTokens elf) (Cli.cliProg cliImg (cliExternsWith ext))
      (entryOf cliImg Cli.mainName) (MuslExit.muslFiniFr elf.entry)
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre cliImg A Cli.MainHops.cliMainStk (Cli.cliStatics cliImg)) :=
  muslHarness_cliImg_of_elf_pool hE htok hMusl hend hfS hfE hmainOff hfz hstat hOk.poolEmp
    (cliExternsWith ext)

/-- Harness-generic whole-binary composer combining `CliElfCodeMatches elf` and
`CliElfTokenCells elf` with `Cli.MuslHarness (patchElfTokens elf)`. -/
theorem cliBinaryCorrect_of_harness {elf : ElfImage} {Fr : SepProp}
    (hcode : CliElfCodeMatches elf)
    (hE : Cli.ElfStaticOk elf)
    (htok : CliElfTokenCells elf)
    (hH : ∀ W : CliHooks,
      Cli.MuslHarness (patchElfTokens elf) (Cli.cliProg cliImg (cliExterns W))
        (entryOf cliImg Cli.mainName) Fr
        (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
        (Cli.mainEntryPre cliImg HooksE.A0 Cli.MainHops.cliMainStk (Cli.cliStatics cliImg)))
    (hmain : MainOkCliSm cliImg) :
    CliBinaryCorrect elf :=
  cliBinaryCorrect_of_parts_observe loads_cliImg cliImg_base hcode
    (fun i => loadState_patchElfTokens hE htok (cliProcessInputs i))
    (elfStaticOk_patchElfTokens hE) hH hmain

/-- Segment-slice whole-binary composer combining `Cli.muslHarness_ok`, `CliElfTokenCells`,
`CliElfFrozen`, `CliElfStatics (patchElfTokens elf) cliImg`, and `MainOkCliSm cliImg` to conclude
`CliBinaryCorrect elf`. -/
theorem cliBinaryCorrect_of_elf {elf : ElfImage} {muslCode : List (BitVec 8)}
    (hE : Cli.ElfStaticOk elf)
    (htok : CliElfTokenCells elf)
    (hMusl : CliElfMusl elf muslCode)
    (hend : cliBase.toNat + libsignalSessionImage.code.length ≤ elf.entry.toNat)
    (hfS : MuslStart.MuslStartFetch ({ code := muslCode } : Program) 0#64)
    (hfE : MuslExit.MuslExitFetch ({ code := muslCode } : Program) 0#64)
    (hmainOff : entryOf cliImg Cli.mainName = elf.entry - muslMainDelta)
    (hfz : CliElfFrozen elf cliImg)
    (hstat : CliElfStatics (patchElfTokens elf) cliImg)
    (hmain : MainOkCliSm cliImg) :
    CliBinaryCorrect elf :=
  cliBinaryCorrect_of_harness (hfz.codeMatches cliImg_base hE) hE htok
    (muslHarness_cliImg_of_elf hE htok hMusl hend hfS hfE hmainOff hfz hstat) hmain

/-- Harness-generic bytes composer (`ElfImage.parse` → `LibsignalCliBinaryCorrect bytes`). -/
theorem libsignalCliBinaryCorrect_of_harness {bytes : List (BitVec 8)} {elf : ElfImage}
    {Fr : SepProp}
    (hparse : ElfImage.parse bytes = .ok elf)
    (hcode : CliElfCodeMatches elf)
    (hE : Cli.ElfStaticOk elf)
    (htok : CliElfTokenCells elf)
    (hH : ∀ W : CliHooks,
      Cli.MuslHarness (patchElfTokens elf) (Cli.cliProg cliImg (cliExterns W))
        (entryOf cliImg Cli.mainName) Fr
        (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
        (Cli.mainEntryPre cliImg HooksE.A0 Cli.MainHops.cliMainStk (Cli.cliStatics cliImg)))
    (hmain : MainOkCliSm cliImg) :
    LibsignalCliBinaryCorrect bytes :=
  ⟨elf, hparse, cliBinaryCorrect_of_harness hcode hE htok hH hmain⟩

/-- Segment-slice bytes composer (`ElfImage.parse` → `LibsignalCliBinaryCorrect bytes`). -/
theorem libsignalCliBinaryCorrect_of_elf {bytes : List (BitVec 8)} {elf : ElfImage}
    {muslCode : List (BitVec 8)}
    (hparse : ElfImage.parse bytes = .ok elf)
    (hE : Cli.ElfStaticOk elf)
    (htok : CliElfTokenCells elf)
    (hMusl : CliElfMusl elf muslCode)
    (hend : cliBase.toNat + libsignalSessionImage.code.length ≤ elf.entry.toNat)
    (hfS : MuslStart.MuslStartFetch ({ code := muslCode } : Program) 0#64)
    (hfE : MuslExit.MuslExitFetch ({ code := muslCode } : Program) 0#64)
    (hmainOff : entryOf cliImg Cli.mainName = elf.entry - muslMainDelta)
    (hfz : CliElfFrozen elf cliImg)
    (hstat : CliElfStatics (patchElfTokens elf) cliImg)
    (hmain : MainOkCliSm cliImg) :
    LibsignalCliBinaryCorrect bytes :=
  ⟨elf, hparse, cliBinaryCorrect_of_elf hE htok hMusl hend hfS hfE hmainOff hfz hstat hmain⟩

end CryptoVerification.SignalSession
