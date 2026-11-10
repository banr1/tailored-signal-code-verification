/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.DirPeakHelpers
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PureBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget

/-!
# Peak Live-Heap Interface for CLI `Dir` and File Read Callees

`PhaseCreditSpec M` bounds for `decimal`, `path`, `address_text`, `read_file` (`CliIo` doubling
schedule `4096 * 2^j` up to `2 MiB` and `ReadFileRuleEnv` covering `allocBytes1Events`, early path
guard `[]`, `cliIoReadScheduleCaps 9`, and over-cap `rustDeallocEvents 2097152 1`), `GrowOneDirEnv`,
`Dir::get`, `Dir::put`, and `Dir::put_str` under `ModelHyps M` and `DirDomainCaps`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.DirPeakSpec

open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalTripleRatchet (reserveCap)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost)
open CryptoVerification.SignalSession.Cli
  (DirGhost GrowOneDirGhost ReadRule addressText decimalText pathOf)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv
   rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.SpecBudget
  (allocBytes1Events cliIoCapsEvents cliIoReadScheduleCaps)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps (DirDomainCaps)
open LibsignalBinary.Proofs.PeakBudget.DirPeakHelpers
  (cliIoCapEvents cliIoCapEventsGo cliIoCap_pos cliIoReadCaps optLargeLive_le
   phaseCreditSpec_cliIoReadFile_uncond
   phaseCreditSpec_concat_rustRealloc_optLive
   phaseCreditSpec_growOneDir_of_le
   phaseCreditSpec_rustAlloc_optLive)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (ConcatEnv ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PureBudget (GrowOneDirEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)

private theorem phaseCreditSpec_exists {α : Type} {M : AllocCostModel} [HasFineReallocCredit M]
    {P : α → List AllocEvent → Prop} {c l p r : Nat}
    (h : ∀ a, PhaseCreditSpec M (P a) c l p r) :
    PhaseCreditSpec M (fun evs => ∃ a, P a evs) c l p r where
  req_align := fun evs ⟨a, ha⟩ => (h a).req_align evs ha
  credit_le := fun st0 _ ⟨a, ha⟩ => (h a).credit_le st0 ha

private theorem phaseCreditSpec_and_left {M : AllocCostModel} [HasFineReallocCredit M]
    {Q : Prop} {P : List AllocEvent → Prop} {c l p r : Nat}
    (h : Q → PhaseCreditSpec M P c l p r) :
    PhaseCreditSpec M (fun evs => Q ∧ P evs) c l p r where
  req_align := fun evs ⟨hq, hp⟩ => (h hq).req_align evs hp
  credit_le := fun st0 _ ⟨hq, hp⟩ => (h hq).credit_le st0 hp

/-! ## 1. `decimal`, `path`, and `address_text` Envelopes -/

/-- Allocator envelope of `decimal(n : u32)`: allocates up to a 10-byte `String` (`≤ 32` B). -/
def CliDecimalEnv (n : BitVec 32) (evs : List AllocEvent) : Prop :=
  evs = [] ∨ ∃ cap : Nat, (decimalText n.toNat).length ≤ cap ∧ cap ≤ 32 ∧
    SeqEnv (· = rustAllocEvents cap 1) FreeOnlyEvs evs

/-- Allocator envelope of `path(dir, name)`: `String::with_capacity`, `push('/')`, and `push_str`. -/
def CliPathEnv (dir name : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  if dir = [] then
    evs = allocBytes1Events name
  else
    let cap0 := dir.length
    let cap1 := reserveCap cap0 cap0 1
    let need2 := decide (cap1 - (cap0 + 1) < name.length)
    let capFinal := if need2 then reserveCap cap1 (cap0 + 1) name.length else cap1
    ConcatEnv
      (ConcatEnv (· = rustAllocEvents cap0 1) (· = rustReallocEvents cap0 cap1 1))
      (if need2 then (· = rustReallocEvents cap1 capFinal 1) else (· = []))
      evs

/-- Allocator envelope of `address_text(&ProtocolAddress)`: formats `<name>.<device_id>`. -/
def CliAddrTextEnv (g : AddrGhost) (evs : List AllocEvent) : Prop :=
  let maxCap := 4 * g.name.bytes.length + 32
  ∃ cap : Nat, cap ≤ maxCap ∧
    SeqEnv (· = rustAllocEvents cap 1) FreeOnlyEvs evs

def decimalDeltaCum : Nat := 2 * 32 + 9539
def decimalDeltaLive : Nat := 32 + 8195
def decimalDeltaPeak : Nat := 32 + 8195

theorem decimal_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (n : BitVec 32) :
    PhaseCreditSpec M (CliDecimalEnv n) decimalDeltaCum decimalDeltaLive decimalDeltaPeak 32 := by
  unfold decimalDeltaCum decimalDeltaLive decimalDeltaPeak CliDecimalEnv
  have hbr : PhaseCreditSpec M
      (fun evs => ∃ cap : Nat, (decimalText n.toNat).length ≤ cap ∧ cap ≤ 32 ∧
        SeqEnv (· = rustAllocEvents cap 1) FreeOnlyEvs evs)
      (2 * 32 + 9539) (32 + 8195) (32 + 8195) 32 :=
    phaseCreditSpec_exists fun cap =>
      phaseCreditSpec_and_left fun _ =>
        phaseCreditSpec_and_left fun _hcap =>
          ((PhaseCreditSpec.rustAlloc_aff hM (req := cap) (al := 1) (by decide)).seq
            (PhaseCreditSpec.freeOnly_of_hyps hM)).mono
            (by omega) (by omega) (by omega) (by omega)
  exact ((PhaseCreditSpec.nil M).or hbr).mono (by omega) (by omega) (by omega) (by omega)

def pathDeltaCum (maxDir maxName : Nat) : Nat :=
  let maxCap := max (4 * maxDir + maxName + 16) 16
  6 * maxCap + 3 * 9539

def pathDeltaLive (maxDir maxName : Nat) : Nat :=
  max (4 * maxDir + maxName + 16) 16 + 8195

def pathDeltaPeak (maxDir maxName : Nat) : Nat :=
  3 * max (4 * maxDir + maxName + 16) 16 + 2 * 8195

def pathMaxReq (maxDir maxName : Nat) : Nat :=
  max (4 * maxDir + maxName + 16) 16

private theorem pathDeltaLive_le_peak (maxDir maxName : Nat) :
    pathDeltaLive maxDir maxName ≤ pathDeltaPeak maxDir maxName := by
  unfold pathDeltaLive pathDeltaPeak
  omega

theorem path_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {dir name : List (BitVec 8)} {maxDir maxName : Nat}
    (hdir : dir.length ≤ maxDir) (hname : name.length ≤ maxName) :
    PhaseCreditSpec M (CliPathEnv dir name)
      (pathDeltaCum maxDir maxName) (pathDeltaLive maxDir maxName)
      (pathDeltaPeak maxDir maxName) (pathMaxReq maxDir maxName) := by
  unfold pathDeltaCum pathDeltaLive pathDeltaPeak pathMaxReq CliPathEnv
  dsimp only
  set maxCap := max (4 * maxDir + maxName + 16) 16 with hmaxCap
  by_cases hnil : dir = []
  · simp only [hnil, ↓reduceIte]
    unfold allocBytes1Events
    split_ifs
    · exact (PhaseCreditSpec.nil M).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    · exact (PhaseCreditSpec.rustAlloc_aff hM (req := name.length) (al := 1) (by decide)).mono
        (by omega) (by omega) (by omega) (by omega)
  · simp only [hnil, ↓reduceIte]
    have hpos0 : 0 < dir.length := List.length_pos_iff.mpr hnil
    set cap0 := dir.length with hcap0
    set cap1 := reserveCap cap0 cap0 1 with hcap1
    set need2 := decide (cap1 - (cap0 + 1) < name.length)
    set capFinal := if need2 then reserveCap cap1 (cap0 + 1) name.length else cap1 with hcapFinal
    have hc01 : cap0 ≤ cap1 := by
      rw [hcap1]; dsimp only [reserveCap]; omega
    have hc1f : cap1 ≤ capFinal := by
      rw [hcapFinal]; dsimp only [reserveCap]; split_ifs <;> omega
    have hcf_le : capFinal ≤ maxCap := by
      rw [hcapFinal, hcap1, hcap0, hmaxCap]
      dsimp only [reserveCap]
      split_ifs <;> omega
    have hc1_le : cap1 ≤ maxCap := Nat.le_trans hc1f hcf_le
    have hc0_le : cap0 ≤ maxCap := Nat.le_trans hc01 hc1_le
    have hpos1 : 0 < cap1 := Nat.lt_of_lt_of_le hpos0 hc01
    have h0 := phaseCreditSpec_rustAlloc_optLive hM (req := cap0) (al := 1) (by decide)
    have h01 := phaseCreditSpec_concat_rustRealloc_optLive hM h0 (al := 1)
      (by decide) (by omega) hpos0 hc01
    cases hneed : need2
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hlive := optLargeLive_le hM hc1_le
      exact (h01.concat (PhaseCreditSpec.nil M)).mono
        (by omega) (by omega) (by omega) (by omega)
    · simp only [↓reduceIte]
      have h012 := phaseCreditSpec_concat_rustRealloc_optLive hM h01 (al := 1)
        (by decide) (by omega) hpos1 hc1f
      have hlive := optLargeLive_le hM hcf_le
      exact h012.mono (by omega) (by omega) (by omega) (by omega)

def addrTextDeltaCum (maxName : Nat) : Nat :=
  2 * (4 * maxName + 32) + 9539

def addrTextDeltaLive (maxName : Nat) : Nat :=
  (4 * maxName + 32) + 8195

def addrTextDeltaPeak (maxName : Nat) : Nat :=
  (4 * maxName + 32) + 8195

def addrTextMaxReq (maxName : Nat) : Nat :=
  4 * maxName + 32

theorem addrText_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (g : AddrGhost) {maxName : Nat}
    (hname : g.name.bytes.length ≤ maxName) :
    PhaseCreditSpec M (CliAddrTextEnv g)
      (addrTextDeltaCum maxName) (addrTextDeltaLive maxName)
      (addrTextDeltaPeak maxName) (addrTextMaxReq maxName) := by
  unfold addrTextDeltaCum addrTextDeltaLive addrTextDeltaPeak addrTextMaxReq CliAddrTextEnv
  dsimp only
  exact phaseCreditSpec_exists fun cap =>
    phaseCreditSpec_and_left fun _hcap =>
      ((PhaseCreditSpec.rustAlloc_aff hM (req := cap) (al := 1) (by decide)).seq
        (PhaseCreditSpec.freeOnly_of_hyps hM)).mono
        (by omega) (by omega) (by omega) (by omega)

/-! ## 2. `allocBytes1Events` and `read_file` (`CliIo` Doubling and `ReadFileRuleEnv`) -/

def allocBytes1DeltaCum (maxLen : Nat) : Nat := 2 * maxLen + 9539
def allocBytes1DeltaLive (maxLen : Nat) : Nat := maxLen + 8195
def allocBytes1DeltaPeak (maxLen : Nat) : Nat := maxLen + 8195

private theorem allocBytes1DeltaLive_eq_peak (maxLen : Nat) :
    allocBytes1DeltaLive maxLen = allocBytes1DeltaPeak maxLen :=
  rfl

theorem allocBytes1_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {bs : List (BitVec 8)} {maxLen : Nat}
    (hlen : bs.length ≤ maxLen) :
    PhaseCreditSpec M (· = allocBytes1Events bs)
      (allocBytes1DeltaCum maxLen) (allocBytes1DeltaLive maxLen)
      (allocBytes1DeltaPeak maxLen) maxLen := by
  unfold allocBytes1DeltaCum allocBytes1DeltaLive allocBytes1DeltaPeak allocBytes1Events
  split_ifs
  · exact (PhaseCreditSpec.nil M).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  · exact (PhaseCreditSpec.rustAlloc_aff hM (req := bs.length) (al := 1) (by decide)).mono
      (by omega) (by omega) (by omega) hlen

def CliIoReadFileEnv (r : Nat) (evs : List AllocEvent) : Prop :=
  evs = cliIoCapEvents (cliIoReadCaps 9 r)

def readFileCliIoDeltaCum : Nat := 8475806
def readFileCliIoDeltaLive : Nat := 2105347
def readFileCliIoDeltaPeak : Nat := 3162118
def readFileCliIoMaxReq : Nat := 2097152

theorem readFile_cliIo_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (r : Nat) :
    PhaseCreditSpec M (CliIoReadFileEnv r)
      readFileCliIoDeltaCum readFileCliIoDeltaLive
      readFileCliIoDeltaPeak readFileCliIoMaxReq := by
  unfold readFileCliIoDeltaCum readFileCliIoDeltaLive readFileCliIoDeltaPeak
    readFileCliIoMaxReq CliIoReadFileEnv
  exact phaseCreditSpec_cliIoReadFile_uncond hM r

private theorem specCliIoCap_eq :
    LibsignalBinary.Heap.SpecBudget.cliIoCap = DirPeakHelpers.cliIoCap :=
  rfl

private theorem specCliIoCapIdx_eq : ∀ (K r : Nat),
    LibsignalBinary.Heap.SpecBudget.cliIoCapIdx K r =
      DirPeakHelpers.cliIoCapIdx K r
  | 0, _ => rfl
  | K + 1, r => by
    unfold LibsignalBinary.Heap.SpecBudget.cliIoCapIdx DirPeakHelpers.cliIoCapIdx
    rw [specCliIoCap_eq, specCliIoCapIdx_eq K r]

private theorem specCliIoCapsEvents_pos_eq :
    ∀ {prev : Nat} (cs : List Nat), 0 < prev → (∀ c ∈ cs, 0 < c) →
      cliIoCapsEvents prev cs = cliIoCapEventsGo prev cs
  | prev, [], _, _ => by cases prev <;> rfl
  | prev, c :: cs, hprev, hcs => by
    cases prev with
    | zero => omega
    | succ m =>
      have hc : 0 < c := hcs c List.mem_cons_self
      have hrest : ∀ x ∈ cs, 0 < x := fun x hx => hcs x (List.mem_cons_of_mem c hx)
      dsimp only [cliIoCapsEvents, cliIoCapEventsGo]
      rw [specCliIoCapsEvents_pos_eq cs hc hrest]

private theorem specCliIoReadSchedule_events_eq (K r : Nat) :
    cliIoCapsEvents 0 (cliIoReadScheduleCaps K r) =
      cliIoCapEvents (cliIoReadCaps K r) := by
  unfold cliIoReadScheduleCaps cliIoReadCaps
  rw [specCliIoCap_eq, specCliIoCapIdx_eq K r]
  split_ifs with hr
  · rfl
  · have hpos : ∀ c ∈ (List.range (DirPeakHelpers.cliIoCapIdx K r + 1)).map
        DirPeakHelpers.cliIoCap, 0 < c := by
      intro c hc
      rcases List.mem_map.mp hc with ⟨j, _, rfl⟩
      exact cliIoCap_pos j
    cases hlist : (List.range (DirPeakHelpers.cliIoCapIdx K r + 1)).map
        DirPeakHelpers.cliIoCap with
    | nil => rfl
    | cons c0 cs =>
      rw [hlist] at hpos
      dsimp only [cliIoCapsEvents, cliIoCapEvents]
      rw [specCliIoCapsEvents_pos_eq cs (hpos c0 List.mem_cons_self)
        (fun x hx => hpos x (List.mem_cons_of_mem c0 hx))]

def readFileRuleDeltaCum (fileCap : Nat) : Nat :=
  max (allocBytes1DeltaCum fileCap) readFileCliIoDeltaCum

def readFileRuleDeltaLive (fileCap : Nat) : Nat :=
  max (allocBytes1DeltaLive fileCap) readFileCliIoDeltaLive

def readFileRuleDeltaPeak (fileCap : Nat) : Nat :=
  max (allocBytes1DeltaPeak fileCap) readFileCliIoDeltaPeak

def readFileRuleMaxReq (fileCap : Nat) : Nat :=
  max fileCap readFileCliIoMaxReq

private theorem readFileRuleDeltaLive_le_peak (fileCap : Nat) :
    readFileRuleDeltaLive fileCap ≤ readFileRuleDeltaPeak fileCap := by
  unfold readFileRuleDeltaLive readFileRuleDeltaPeak
    allocBytes1DeltaLive allocBytes1DeltaPeak
    readFileCliIoDeltaLive readFileCliIoDeltaPeak
  omega

theorem readFile_rule_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (rd : ReadRule) (files : FsFiles) (path : List (BitVec 8))
    {fileCap : Nat}
    (hcap : ∀ bs, rd files path = .ok bs → bs.length ≤ fileCap) :
    PhaseCreditSpec M (ReadFileRuleEnv rd files path)
      (readFileRuleDeltaCum fileCap) (readFileRuleDeltaLive fileCap)
      (readFileRuleDeltaPeak fileCap) (readFileRuleMaxReq fileCap) := by
  unfold ReadFileRuleEnv
  cases hrd : rd files path with
  | error u =>
    cases u
    exact (PhaseCreditSpec.nil M).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  | ok bs =>
    dsimp only
    have h1 : PhaseCreditSpec M (fun evs => evs = allocBytes1Events bs)
        (readFileRuleDeltaCum fileCap) (readFileRuleDeltaLive fileCap)
        (readFileRuleDeltaPeak fileCap) (readFileRuleMaxReq fileCap) :=
      (allocBytes1_phaseCredit hM (hcap bs hrd)).mono
        (Nat.le_max_left _ _) (Nat.le_max_left _ _)
        (Nat.le_max_left _ _) (Nat.le_max_left _ _)
    have h2 : PhaseCreditSpec M
        (fun evs => (4096 ≤ path.length ∨ 0#8 ∈ path) ∧ evs = [])
        (readFileRuleDeltaCum fileCap) (readFileRuleDeltaLive fileCap)
        (readFileRuleDeltaPeak fileCap) (readFileRuleMaxReq fileCap) :=
      (PhaseCreditSpec.of_eq_nil (M := M) (fun _ h => h.2)).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    have h3 : PhaseCreditSpec M
        (fun evs => bs.length ≤ 2097152 ∧
          evs = cliIoCapsEvents 0 (cliIoReadScheduleCaps 9 bs.length))
        (readFileRuleDeltaCum fileCap) (readFileRuleDeltaLive fileCap)
        (readFileRuleDeltaPeak fileCap) (readFileRuleMaxReq fileCap) :=
      (readFile_cliIo_phaseCredit hM bs.length).congr_mono
        (fun evs h => by
          unfold CliIoReadFileEnv
          rw [← specCliIoReadSchedule_events_eq 9 bs.length]
          exact h.2)
        (Nat.le_max_right _ _) (Nat.le_max_right _ _)
        (Nat.le_max_right _ _) (Nat.le_max_right _ _)
    have h4 : PhaseCreditSpec M
        (fun evs => 2097152 < bs.length ∧
          evs = cliIoCapsEvents 0 (cliIoReadScheduleCaps 9 2097152) ++
            rustDeallocEvents 2097152 1)
        (readFileRuleDeltaCum fileCap) (readFileRuleDeltaLive fileCap)
        (readFileRuleDeltaPeak fileCap) (readFileRuleMaxReq fileCap) := by
      have hseq := (readFile_cliIo_phaseCredit hM 2097152).seq
        (PhaseCreditSpec.freeOnly_of_hyps hM)
      refine hseq.congr_mono ?_ ?_ ?_ ?_ ?_
      · intro evs h
        refine Or.inr ⟨_, _, h.2, ?_, ?_⟩
        · unfold CliIoReadFileEnv
          exact specCliIoReadSchedule_events_eq 9 2097152
        · unfold FreeOnlyEvs rustDeallocEvents
          intro ev hev
          rw [List.mem_singleton] at hev
          exact ⟨1, 2097152, hev⟩
      · unfold readFileRuleDeltaCum; omega
      · unfold readFileRuleDeltaLive; omega
      · unfold readFileRuleDeltaPeak readFileCliIoDeltaPeak readFileCliIoDeltaLive; omega
      · unfold readFileRuleMaxReq; omega
    exact (h1.or (h2.or (h3.or h4))).mono
      (by omega) (by omega) (by omega) (by omega)

/-! ## 3. `GrowOneDir`, `Dir::get`, `Dir::put`, and `Dir::put_str` -/

def growOneDirDeltaCum (maxEntries : Nat) : Nat :=
  2 * (48 * max 4 (2 * maxEntries)) + 9539

def growOneDirDeltaLive (maxEntries : Nat) : Nat :=
  48 * max 4 (2 * maxEntries) + 8195

def growOneDirDeltaPeak (maxEntries : Nat) : Nat :=
  48 * max 4 (2 * maxEntries) + 8195

def growOneDirMaxReq (maxEntries : Nat) : Nat :=
  48 * max 4 (2 * maxEntries)

theorem growOneDir_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {x : GrowOneDirGhost} {maxEntries : Nat}
    (hcap : x.cap.toNat ≤ maxEntries) :
    PhaseCreditSpec M (GrowOneDirEnv x)
      (growOneDirDeltaCum maxEntries) (growOneDirDeltaLive maxEntries)
      (growOneDirDeltaPeak maxEntries) (growOneDirMaxReq maxEntries) := by
  unfold growOneDirDeltaCum growOneDirDeltaLive growOneDirDeltaPeak growOneDirMaxReq GrowOneDirEnv
  exact phaseCreditSpec_growOneDir_of_le hM x.cap hcap

/-- `Dir::get`: cache hit clones existing `v` (`allocBytes1Events v`), or cache miss builds
`CliPathEnv dir.path name`, runs `ReadEnv files (pathOf dir.path name)`, and drops `path` (`FreeOnlyEvs`). -/
def CliDirGetEnv (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (files : FsFiles) (dir : DirGhost) (name : List (BitVec 8))
    (evs : List AllocEvent) : Prop :=
  (∃ k v, (k, v) ∈ dir.changed ∧ k = name ∧ evs = allocBytes1Events v) ∨
  SeqEnv (CliPathEnv dir.path name)
    (SeqEnv (ReadEnv files (pathOf dir.path name)) FreeOnlyEvs)
    evs

def dirGetRuleDeltaCum (maxDir maxName maxVal fileCap : Nat) : Nat :=
  max (allocBytes1DeltaCum maxVal) (pathDeltaCum maxDir maxName + readFileRuleDeltaCum fileCap)

def dirGetRuleDeltaLive (maxDir maxName maxVal fileCap : Nat) : Nat :=
  max (allocBytes1DeltaLive maxVal) (pathDeltaLive maxDir maxName + readFileRuleDeltaLive fileCap)

def dirGetRuleDeltaPeak (maxDir maxName maxVal fileCap : Nat) : Nat :=
  max (allocBytes1DeltaPeak maxVal) (pathDeltaPeak maxDir maxName + readFileRuleDeltaPeak fileCap)

def dirGetRuleMaxReq (maxDir maxName maxVal fileCap : Nat) : Nat :=
  max maxVal (max (pathMaxReq maxDir maxName) (readFileRuleMaxReq fileCap))

theorem dirGet_rule_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (rd : ReadRule) (files : FsFiles) (dir : DirGhost)
    (name : List (BitVec 8)) {maxDir maxEntries maxVal maxName fileCap : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir)
    (hname : name.length ≤ maxName)
    (hcap : ∀ bs, rd files (pathOf dir.path name) = .ok bs → bs.length ≤ fileCap) :
    PhaseCreditSpec M (CliDirGetEnv (ReadFileRuleEnv rd) files dir name)
      (dirGetRuleDeltaCum maxDir maxName maxVal fileCap)
      (dirGetRuleDeltaLive maxDir maxName maxVal fileCap)
      (dirGetRuleDeltaPeak maxDir maxName maxVal fileCap)
      (dirGetRuleMaxReq maxDir maxName maxVal fileCap) := by
  let _ := maxEntries
  unfold dirGetRuleDeltaCum dirGetRuleDeltaLive dirGetRuleDeltaPeak dirGetRuleMaxReq CliDirGetEnv
  have hhit : PhaseCreditSpec M
      (fun evs => ∃ k v, (k, v) ∈ dir.changed ∧ k = name ∧ evs = allocBytes1Events v)
      (allocBytes1DeltaCum maxVal) (allocBytes1DeltaLive maxVal)
      (allocBytes1DeltaPeak maxVal) maxVal :=
    phaseCreditSpec_exists fun k =>
      phaseCreditSpec_exists fun v =>
        phaseCreditSpec_and_left fun hmem =>
          phaseCreditSpec_and_left fun _ =>
            allocBytes1_phaseCredit hM (hdc.changed_val_le k v hmem)
  have hpath := path_phaseCredit hM hdc.path_len_le hname
  have hrd := (readFile_rule_phaseCredit hM rd files (pathOf dir.path name) hcap).seq
    (PhaseCreditSpec.freeOnly_of_hyps hM)
  have hmiss := hpath.seq hrd
  have hpl := pathDeltaLive_le_peak maxDir maxName
  have hal := readFileRuleDeltaLive_le_peak fileCap
  have hmiss' : PhaseCreditSpec M
      (SeqEnv (CliPathEnv dir.path name)
        (SeqEnv (ReadFileRuleEnv rd files (pathOf dir.path name)) FreeOnlyEvs))
      (pathDeltaCum maxDir maxName + readFileRuleDeltaCum fileCap)
      (pathDeltaLive maxDir maxName + readFileRuleDeltaLive fileCap)
      (pathDeltaPeak maxDir maxName + readFileRuleDeltaPeak fileCap)
      (max (pathMaxReq maxDir maxName) (readFileRuleMaxReq fileCap)) :=
    hmiss.mono (by omega) (by omega) (by omega) (by omega)
  exact hhit.or hmiss'

/-- `Dir::put`: either overwrites an existing entry in place (`FreeOnlyEvs` dropping old key + value)
or grows `dir.changed` by one `48`-byte `(String, Vec<u8>)` slot (`GrowOneDirEnv`). -/
def CliDirPutEnv (dir : DirGhost) (_name _bytes : List (BitVec 8))
    (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
  (∃ x : GrowOneDirGhost, x.cap.toNat ≤ max 4 (2 * dir.changed.length) ∧ GrowOneDirEnv x evs)

/-- `Dir::put_str`: allocates owned `name` (`allocBytes1Events name`) followed by `CliDirPutEnv`. -/
def CliDirPutStrEnv (dir : DirGhost) (name bytes : List (BitVec 8))
    (evs : List AllocEvent) : Prop :=
  SeqEnv (· = allocBytes1Events name) (CliDirPutEnv dir name bytes) evs

def dirPutDeltaCum (maxEntries : Nat) : Nat :=
  growOneDirDeltaCum (max 4 (2 * maxEntries))

def dirPutDeltaLive (maxEntries : Nat) : Nat :=
  growOneDirDeltaLive (max 4 (2 * maxEntries))

def dirPutDeltaPeak (maxEntries : Nat) : Nat :=
  growOneDirDeltaPeak (max 4 (2 * maxEntries))

def dirPutMaxReq (maxEntries : Nat) : Nat :=
  growOneDirMaxReq (max 4 (2 * maxEntries))

theorem dirPut_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (dir : DirGhost) (name bytes : List (BitVec 8))
    {maxDir maxEntries maxVal : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir) :
    PhaseCreditSpec M (CliDirPutEnv dir name bytes)
      (dirPutDeltaCum maxEntries) (dirPutDeltaLive maxEntries)
      (dirPutDeltaPeak maxEntries) (dirPutMaxReq maxEntries) := by
  let _ := (name, bytes, maxDir, maxVal)
  unfold dirPutDeltaCum dirPutDeltaLive dirPutDeltaPeak dirPutMaxReq CliDirPutEnv
  have hgrow : PhaseCreditSpec M
      (fun evs => ∃ x : GrowOneDirGhost,
        x.cap.toNat ≤ max 4 (2 * dir.changed.length) ∧ GrowOneDirEnv x evs)
      (growOneDirDeltaCum (max 4 (2 * maxEntries)))
      (growOneDirDeltaLive (max 4 (2 * maxEntries)))
      (growOneDirDeltaPeak (max 4 (2 * maxEntries)))
      (growOneDirMaxReq (max 4 (2 * maxEntries))) :=
    phaseCreditSpec_exists fun x =>
      phaseCreditSpec_and_left fun hx => by
        have hcap' : x.cap.toNat ≤ max 4 (2 * maxEntries) := by
          have := hdc.changed_len_le
          omega
        exact growOneDir_phaseCredit hM hcap'
  exact ((PhaseCreditSpec.freeOnly_of_hyps hM).or hgrow).mono
    (by omega) (by omega) (by omega) (by omega)

def dirPutStrDeltaCum (maxName maxEntries : Nat) : Nat :=
  allocBytes1DeltaCum maxName + dirPutDeltaCum maxEntries

def dirPutStrDeltaLive (maxName maxEntries : Nat) : Nat :=
  allocBytes1DeltaLive maxName + dirPutDeltaLive maxEntries

def dirPutStrDeltaPeak (maxName maxEntries : Nat) : Nat :=
  allocBytes1DeltaPeak maxName + dirPutDeltaPeak maxEntries

def dirPutStrMaxReq (maxName maxEntries : Nat) : Nat :=
  max maxName (dirPutMaxReq maxEntries)

theorem dirPutStr_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (dir : DirGhost) (name bytes : List (BitVec 8))
    {maxDir maxEntries maxVal maxName : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir)
    (hname : name.length ≤ maxName) :
    PhaseCreditSpec M (CliDirPutStrEnv dir name bytes)
      (dirPutStrDeltaCum maxName maxEntries)
      (dirPutStrDeltaLive maxName maxEntries)
      (dirPutStrDeltaPeak maxName maxEntries)
      (dirPutStrMaxReq maxName maxEntries) := by
  let _ := (maxDir, maxVal)
  unfold dirPutStrDeltaCum dirPutStrDeltaLive dirPutStrDeltaPeak dirPutStrMaxReq CliDirPutStrEnv
  have h1 := allocBytes1_phaseCredit hM hname
  have h2 := dirPut_phaseCredit hM dir name bytes hdc
  have hal := allocBytes1DeltaLive_eq_peak maxName
  exact (h1.seq h2).mono (Nat.le_refl _) (Nat.le_refl _) (by omega) (Nat.le_refl _)

end LibsignalBinary.Proofs.PeakBudget.DirPeakSpec
