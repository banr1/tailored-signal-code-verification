/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.ClientBounds
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.CliMainIoCredit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget

/-!
# Peak Live-Heap Specification for `signal-session` `main` Phases M1–M6

Sequential `SeqEnv` live-heap credit specification for `Cli.main` (`M1` argv buffer → `M2` collect +
`address` → `M3` `read_stdin` + `"coins"` `read_file` → `M4` `RunEnv g` → `M5` dirty-file commit +
store drops → `M6` `1024`-B `LineWriter` `write_stdout` before final drops), parametric over
`M : AllocCostModel` and `RunEnv : RunCall → List AllocEvent → Prop`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec

open _root_.Arm64 (FsEntry)
open _root_.Arm64.Process (initFsState)
open CryptoVerification.E2E.Pqxdh.Shared (TryAllocateInCall)
open CryptoVerification.LibsignalTripleRatchet (reserveCap)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.SignalSession (Inputs)
open CryptoVerification.SignalSession.Cli (cliInputs pathOf utf8)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV AddressCall CallV Reserve16Call RunCall)
open CryptoVerification.SpqrV1.Alloc (reserveCapStride)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv
   rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds (fineCostModel_smallMaxReq_eq)
open LibsignalBinary.Heap.SpecBudget (ReadFileEnv ReadStdinEnv)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps (CliPqDomainCaps FilesBounded)
open LibsignalBinary.Proofs.PeakBudget.CliMainIoCredit
  (CliIoReadFileEnv CliIoReadStdinEnv
   phaseCreditSpec_cliIoReadFile_anyR_tight phaseCreditSpec_cliIoReadStdin_anyR_tight
   phaseCredit_address phaseCredit_address_cap40 phaseCredit_address_small64
   phaseCredit_cliWriteFile phaseCredit_cliWriteStdout phaseCredit_cliWriteStdout_small1024
   phaseCredit_m1Phase phaseCredit_m1Phase_small64
   phaseCredit_m2Collect phaseCredit_m2Collect_small64 phaseCredit_m5LoopAEntry
   phaseCredit_readFile_of_files_le phaseCredit_readFile_of_files_le_tight
   phaseCredit_readStdin phaseCredit_readStdin_tight
   phaseCredit_reserve16 phaseCredit_tryAllocateIn
   readFile_cliIo_phaseCredit_tight readStdin_cliIo_phaseCredit_tight)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (ConcatEnv IterSeqEnv ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget
  (AddressEnv Reserve16Env TryAllocateInEnv)

/-- Allocation envelope for `signal_session_io::write_file`. -/
def CliWriteFileEnv (len : Nat) (evs : List AllocEvent) : Prop :=
  evs = [] ∨
  (384 ≤ len ∧ evs = rustAllocEvents (len + 1) 1 ++ rustDeallocEvents (len + 1) 1)

/-- Allocation envelope for `signal_session_io::write_stdout` (`1024`-B `LineWriter`). -/
def CliWriteStdoutEnv (evs : List AllocEvent) : Prop :=
  evs = [] ∨ evs = rustAllocEvents 1024 1

/-! ## Callee Envelopes (`address`, `reserve16`, `try_allocate_in`) -/

def addressDeltaCum (x : AddressCall) : Nat :=
  2 * x.bs.length + 28617

def addressDeltaLive (x : AddressCall) : Nat :=
  x.bs.length + 8195

def addressDeltaPeak (x : AddressCall) : Nat :=
  x.bs.length + 16390

def addressMaxReq (x : AddressCall) : Nat :=
  max 48 x.bs.length

theorem address_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (uuidParse : UuidParser) (x : AddressCall) :
    PhaseCreditSpec M (AddressEnv uuidParse x)
      (addressDeltaCum x) (addressDeltaLive x) (addressDeltaPeak x) (addressMaxReq x) := by
  exact phaseCredit_address hM uuidParse x

def reserve16DeltaCum (newCap : Nat) : Nat :=
  32 * newCap + 9539

def reserve16DeltaLive (newCap : Nat) : Nat :=
  16 * newCap + 8195

def reserve16DeltaPeak (newCap : Nat) : Nat :=
  16 * newCap + 8195

theorem reserve16_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (x : Reserve16Call) :
    let curLen := x.bs.length / 16
    let newCap := reserveCapStride 16 x.cap.toNat curLen 1
    PhaseCreditSpec M (Reserve16Env x)
      (reserve16DeltaCum newCap) (reserve16DeltaLive newCap)
      (reserve16DeltaPeak newCap) (16 * newCap) := by
  exact phaseCredit_reserve16 hM x

def tryAllocateInDeltaCum (req : Nat) : Nat :=
  2 * req + 9539

def tryAllocateInDeltaLive (req : Nat) : Nat :=
  req + 8195

def tryAllocateInDeltaPeak (req : Nat) : Nat :=
  req + 8195

theorem tryAllocateIn_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (x : TryAllocateInCall)
    (hal : x.align.toNat ≤ 16) :
    let req := x.new.toNat * x.stride.toNat
    PhaseCreditSpec M (TryAllocateInEnv x)
      (tryAllocateInDeltaCum req)
      (tryAllocateInDeltaLive req)
      (tryAllocateInDeltaPeak req)
      req := by
  exact phaseCredit_tryAllocateIn hM x hal

/-! ## Phase M1–M3 Envelopes (`argv`, `read_stdin`, `"coins"` `read_file`) -/

def M1PhaseEnv (argvLen : Nat) (evs : List AllocEvent) : Prop :=
  evs = [] ∨ evs = rustAllocEvents (16 * argvLen) 8

def M2CollectStepEnv (k : Nat) (evs : List AllocEvent) : Prop :=
  evs = [] ∨ evs = rustReallocEvents (16 * k) (16 * reserveCapStride 16 k k 1) 8

def M2CollectEnv (argvLen : Nat) (evs : List AllocEvent) : Prop :=
  IterSeqEnv M2CollectStepEnv (List.range argvLen) evs

def M3PhaseEnv (needStdin : Bool) (stdin : List (BitVec 8))
    (files : String → Option FsEntry) (coinsPath : List (BitVec 8))
    (evs : List AllocEvent) : Prop :=
  SeqEnv
    (if needStdin then ReadStdinEnv stdin else (· = []))
    (SeqEnv (ReadFileEnv files coinsPath) FreeOnlyEvs)
    evs

def readStdinDeltaCum (stdinCap : Nat) : Nat :=
  max (2 * stdinCap + 9539) (4 * 1048576 + 9 * 9539)

def readStdinDeltaLive (stdinCap : Nat) : Nat :=
  max (stdinCap + 8195) (1048576 + 8195)

def readStdinDeltaPeak (stdinCap : Nat) : Nat :=
  max (stdinCap + 8195) 1589254

def readStdinMaxReq (stdinCap : Nat) : Nat :=
  max stdinCap 1048576

theorem readStdin_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (stdin : List (BitVec 8)) {stdinCap : Nat}
    (hstdin : stdin.length ≤ stdinCap) :
    PhaseCreditSpec M (ReadStdinEnv stdin)
      (readStdinDeltaCum stdinCap) (readStdinDeltaLive stdinCap)
      (readStdinDeltaPeak stdinCap) (readStdinMaxReq stdinCap) := by
  unfold readStdinDeltaCum readStdinDeltaLive readStdinDeltaPeak readStdinMaxReq
  exact (phaseCredit_readStdin hM stdin hstdin).mono
    (by omega) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

def m3PhaseDeltaCum (stdinCap fileCap : Nat) : Nat :=
  readStdinDeltaCum stdinCap + max (2 * fileCap + 9539) (4 * 2097152 + 10 * 9539)

def m3PhaseDeltaLive (stdinCap fileCap : Nat) : Nat :=
  readStdinDeltaLive stdinCap + max (fileCap + 8195) (2097152 + 8195)

def m3PhaseDeltaPeak (stdinCap fileCap : Nat) : Nat :=
  max (readStdinDeltaPeak stdinCap)
    (readStdinDeltaLive stdinCap + max (fileCap + 8195) 3162118)

def m3PhaseMaxReq (stdinCap fileCap : Nat) : Nat :=
  max (readStdinMaxReq stdinCap) (max fileCap 2097152)

theorem m3Phase_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (needStdin : Bool) (stdin : List (BitVec 8))
    (files : String → Option FsEntry) (coinsPath : List (BitVec 8))
    {stdinCap fileCap : Nat}
    (hstdin : stdin.length ≤ stdinCap)
    (hfb : ∀ p bs, files p = some (.file bs) → bs.length ≤ fileCap) :
    PhaseCreditSpec M (M3PhaseEnv needStdin stdin files coinsPath)
      (m3PhaseDeltaCum stdinCap fileCap)
      (m3PhaseDeltaLive stdinCap fileCap)
      (m3PhaseDeltaPeak stdinCap fileCap)
      (m3PhaseMaxReq stdinCap fileCap) := by
  have hst : PhaseCreditSpec M (if needStdin then ReadStdinEnv stdin else (· = []))
      (readStdinDeltaCum stdinCap) (readStdinDeltaLive stdinCap)
      (readStdinDeltaPeak stdinCap) (readStdinMaxReq stdinCap) := by
    cases needStdin
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact (PhaseCreditSpec.nil M).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    · simp only [↓reduceIte]
      exact readStdin_phaseCredit hM stdin hstdin
  have hrf : PhaseCreditSpec M (SeqEnv (ReadFileEnv files coinsPath) FreeOnlyEvs)
      (max (2 * fileCap + 9539) (4 * 2097152 + 10 * 9539))
      (max (fileCap + 8195) (2097152 + 8195))
      (max (fileCap + 8195) 3162118)
      (max fileCap 2097152) := by
    refine ((phaseCredit_readFile_of_files_le hM files coinsPath hfb).seq
      (PhaseCreditSpec.freeOnly hM.freeNonInc)).mono ?_ ?_ ?_ ?_
    · omega
    · omega
    · omega
    · omega
  exact hst.seq hrf

/-- Tight `read_stdin` (`j = 8` doubling / single-buffer) `cumSmall` bound (`573,696` B). -/
def readStdinDeltaCum_tight : Nat := 573696

/-- Tight `"coins"` `read_file` (`j = 9` doubling / single-buffer) `cumSmall` bound (`573,818` B). -/
def readFileDeltaCum_tight : Nat := 573818

/-- Tight Phase-M3 `cumSmall` bound (`573,696 + 573,818 = 1,147,514` B). -/
def m3PhaseDeltaCum_tight : Nat :=
  readStdinDeltaCum_tight + readFileDeltaCum_tight

/-- `CliIo` doubling-schedule Phase-M3 envelope (`j = 8` `read_stdin` + `j = 9` `"coins"` `read_file`
followed by drop frees). -/
def M3PhaseCliIoEnv (needStdin : Bool) (stdinLen fileLen : Nat) (evs : List AllocEvent) : Prop :=
  SeqEnv
    (if needStdin then CliIoReadStdinEnv stdinLen else (· = []))
    (SeqEnv (CliIoReadFileEnv fileLen) FreeOnlyEvs)
    evs

/-- Tight `ReadStdinEnv` `PhaseCreditSpec` (`Δcum = 573,696` B) when
`131072 ≤ smallMaxReq M < 262144`. -/
theorem readStdin_phaseCredit_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M)
    (hSmLo : 131072 ≤ HasFineReallocCredit.smallMaxReq M)
    (hSmHi : HasFineReallocCredit.smallMaxReq M < 262144)
    (stdin : List (BitVec 8)) {stdinCap : Nat}
    (hstdin : stdin.length ≤ stdinCap) :
    PhaseCreditSpec M (ReadStdinEnv stdin)
      readStdinDeltaCum_tight (readStdinDeltaLive stdinCap)
      (readStdinDeltaPeak stdinCap) (readStdinMaxReq stdinCap) := by
  unfold readStdinDeltaCum_tight readStdinDeltaLive readStdinDeltaPeak readStdinMaxReq
  exact phaseCredit_readStdin_tight hM hSmLo hSmHi stdin hstdin

/-- Tight `M3PhaseEnv` `PhaseCreditSpec` (`Δcum = 1,147,514` B) when
`131072 ≤ smallMaxReq M < 262144`. -/
theorem m3Phase_phaseCredit_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M)
    (hSmLo : 131072 ≤ HasFineReallocCredit.smallMaxReq M)
    (hSmHi : HasFineReallocCredit.smallMaxReq M < 262144)
    (needStdin : Bool) (stdin : List (BitVec 8))
    (files : String → Option FsEntry) (coinsPath : List (BitVec 8))
    {stdinCap fileCap : Nat}
    (hstdin : stdin.length ≤ stdinCap)
    (hfb : ∀ p bs, files p = some (.file bs) → bs.length ≤ fileCap) :
    PhaseCreditSpec M (M3PhaseEnv needStdin stdin files coinsPath)
      m3PhaseDeltaCum_tight
      (m3PhaseDeltaLive stdinCap fileCap)
      (m3PhaseDeltaPeak stdinCap fileCap)
      (m3PhaseMaxReq stdinCap fileCap) := by
  have hst : PhaseCreditSpec M (if needStdin then ReadStdinEnv stdin else (· = []))
      readStdinDeltaCum_tight (readStdinDeltaLive stdinCap)
      (readStdinDeltaPeak stdinCap) (readStdinMaxReq stdinCap) := by
    cases needStdin
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact (PhaseCreditSpec.nil M).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    · simp only [↓reduceIte]
      exact readStdin_phaseCredit_tight hM hSmLo hSmHi stdin hstdin
  have hrf : PhaseCreditSpec M (SeqEnv (ReadFileEnv files coinsPath) FreeOnlyEvs)
      readFileDeltaCum_tight
      (max (fileCap + 8195) (2097152 + 8195))
      (max (fileCap + 8195) 3162118)
      (max fileCap 2097152) := by
    unfold readFileDeltaCum_tight
    refine ((phaseCredit_readFile_of_files_le_tight hM hSmLo hSmHi files coinsPath hfb).seq
      (PhaseCreditSpec.freeOnly hM.freeNonInc)).mono ?_ ?_ ?_ ?_
    · omega
    · omega
    · omega
    · omega
  exact hst.seq hrf

theorem m3Phase_phaseCredit_fine
    (hM : ModelHyps fineCostModel) (needStdin : Bool) (stdin : List (BitVec 8))
    (files : String → Option FsEntry) (coinsPath : List (BitVec 8))
    {stdinCap fileCap : Nat}
    (hstdin : stdin.length ≤ stdinCap)
    (hfb : ∀ p bs, files p = some (.file bs) → bs.length ≤ fileCap) :
    PhaseCreditSpec fineCostModel (M3PhaseEnv needStdin stdin files coinsPath)
      m3PhaseDeltaCum_tight
      (m3PhaseDeltaLive stdinCap fileCap)
      (m3PhaseDeltaPeak stdinCap fileCap)
      (m3PhaseMaxReq stdinCap fileCap) :=
  m3Phase_phaseCredit_tight hM
    (by rw [fineCostModel_smallMaxReq_eq]; decide)
    (by rw [fineCostModel_smallMaxReq_eq]; decide)
    needStdin stdin files coinsPath hstdin hfb

/-- Tight `M3PhaseCliIoEnv` `PhaseCreditSpec` (`Δcum = 1,147,514` B, `Δlive = 3,162,118` B,
`Δpeak = 4,218,889` B, `maxReq = 2,097,152` B) when `131072 ≤ smallMaxReq M < 262144`. -/
theorem m3Phase_cliIo_phaseCredit_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M)
    (hSmLo : 131072 ≤ HasFineReallocCredit.smallMaxReq M)
    (hSmHi : HasFineReallocCredit.smallMaxReq M < 262144)
    (needStdin : Bool) (stdinLen fileLen : Nat) :
    PhaseCreditSpec M (M3PhaseCliIoEnv needStdin stdinLen fileLen)
      m3PhaseDeltaCum_tight
      (m3PhaseDeltaLive 1048576 2097152)
      (m3PhaseDeltaPeak 1048576 2097152)
      (m3PhaseMaxReq 1048576 2097152) := by
  have hst : PhaseCreditSpec M (if needStdin then CliIoReadStdinEnv stdinLen else (· = []))
      readStdinDeltaCum_tight (readStdinDeltaLive 1048576)
      (readStdinDeltaPeak 1048576) (readStdinMaxReq 1048576) := by
    cases needStdin
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact (PhaseCreditSpec.nil M).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    · simp only [↓reduceIte]
      exact (readStdin_cliIo_phaseCredit_tight hM hSmLo hSmHi stdinLen).mono
        (by decide) (by decide) (by decide) (by decide)
  have hrf : PhaseCreditSpec M (SeqEnv (CliIoReadFileEnv fileLen) FreeOnlyEvs)
      readFileDeltaCum_tight
      (max (2097152 + 8195) (2097152 + 8195))
      (max (2097152 + 8195) 3162118)
      (max 2097152 2097152) := by
    refine ((readFile_cliIo_phaseCredit_tight hM hSmLo hSmHi fileLen).seq
      (PhaseCreditSpec.freeOnly hM.freeNonInc)).mono ?_ ?_ ?_ ?_
    · decide
    · decide
    · decide
    · decide
  exact hst.seq hrf

theorem m3Phase_cliIo_anyR_phaseCredit_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M)
    (hSmLo : 131072 ≤ HasFineReallocCredit.smallMaxReq M)
    (hSmHi : HasFineReallocCredit.smallMaxReq M < 262144)
    (needStdin : Bool) :
    PhaseCreditSpec M
      (SeqEnv
        (if needStdin then (fun e => ∃ r, CliIoReadStdinEnv r e) else (· = []))
        (SeqEnv (fun e => ∃ r, CliIoReadFileEnv r e) FreeOnlyEvs))
      m3PhaseDeltaCum_tight
      (m3PhaseDeltaLive 1048576 2097152)
      (m3PhaseDeltaPeak 1048576 2097152)
      (m3PhaseMaxReq 1048576 2097152) := by
  have hst : PhaseCreditSpec M
      (if needStdin then (fun e => ∃ r, CliIoReadStdinEnv r e) else (· = []))
      readStdinDeltaCum_tight (readStdinDeltaLive 1048576)
      (readStdinDeltaPeak 1048576) (readStdinMaxReq 1048576) := by
    cases needStdin
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact (PhaseCreditSpec.nil M).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    · simp only [↓reduceIte]
      exact (phaseCreditSpec_cliIoReadStdin_anyR_tight hM hSmLo hSmHi).mono
        (by decide) (by decide) (by decide) (by decide)
  have hrf : PhaseCreditSpec M
      (SeqEnv (fun e => ∃ r, CliIoReadFileEnv r e) FreeOnlyEvs)
      readFileDeltaCum_tight
      (max (2097152 + 8195) (2097152 + 8195))
      (max (2097152 + 8195) 3162118)
      (max 2097152 2097152) := by
    refine ((phaseCreditSpec_cliIoReadFile_anyR_tight hM hSmLo hSmHi).seq
      (PhaseCreditSpec.freeOnly hM.freeNonInc)).mono ?_ ?_ ?_ ?_
    · decide
    · decide
    · decide
    · decide
  exact hst.seq hrf

theorem m3Phase_cliIo_phaseCredit_fine
    (hM : ModelHyps fineCostModel) (needStdin : Bool) (stdinLen fileLen : Nat) :
    PhaseCreditSpec fineCostModel (M3PhaseCliIoEnv needStdin stdinLen fileLen)
      m3PhaseDeltaCum_tight
      (m3PhaseDeltaLive 1048576 2097152)
      (m3PhaseDeltaPeak 1048576 2097152)
      (m3PhaseMaxReq 1048576 2097152) :=
  m3Phase_cliIo_phaseCredit_tight hM
    (by rw [fineCostModel_smallMaxReq_eq]; decide)
    (by rw [fineCostModel_smallMaxReq_eq]; decide)
    needStdin stdinLen fileLen

/-! ## Phase M5 (`write_file` Loop and Store Drops) and M6 (`LineWriter` and Final Drops) -/

def M5LoopAEntryEnv (dir name : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  let cap0 := dir.length
  let cap1 := reserveCap cap0 cap0 1
  let need2 := decide (cap1 - (cap0 + 1) < name.length)
  let capFinal := if need2 then reserveCap cap1 (cap0 + 1) name.length else cap1
  ConcatEnv
    (ConcatEnv
      (ConcatEnv
        (ConcatEnv (· = rustAllocEvents cap0 1) (· = rustReallocEvents cap0 cap1 1))
        (if need2 then (· = rustReallocEvents cap1 capFinal 1) else (· = [])))
      (CliWriteFileEnv (pathOf dir name).length))
    (· = rustDeallocEvents capFinal 1)
    evs

def M5WriteStepEnv (entry : List (BitVec 8) × List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  if entry.1 = [] then CliWriteFileEnv entry.2.length evs
  else M5LoopAEntryEnv entry.1 entry.2 evs

def M5DirStepEnv (dir : List (BitVec 8)) (names : List (List (BitVec 8)))
    (evs : List AllocEvent) : Prop :=
  SeqEnv (IterSeqEnv (fun name => M5WriteStepEnv (dir, name)) names) FreeOnlyEvs evs

def M5PhaseEnv (dirs : List (List (BitVec 8) × List (List (BitVec 8))))
    (evs : List AllocEvent) : Prop :=
  SeqEnv (IterSeqEnv (fun dn => M5DirStepEnv dn.1 dn.2) dirs) FreeOnlyEvs evs

def M6Env (ok : Bool) (evs : List AllocEvent) : Prop :=
  SeqEnv (if ok then CliWriteStdoutEnv else (· = [])) FreeOnlyEvs evs

def m5DirStepDeltaCum (numChanged maxDir maxName : Nat) : Nat :=
  let maxCap := max (4 * maxDir + maxName + 16) 16
  numChanged * (10 * maxCap + 4 * 9539)

def m5DirStepDeltaPeak (maxDir maxName : Nat) : Nat :=
  let maxCap := max (4 * maxDir + maxName + 16) 16
  3 * maxCap + 3 * 8195

def m5DirStepMaxReq (maxDir maxName : Nat) : Nat :=
  max (4 * maxDir + maxName + 16) 16

private theorem byteArray_toList_eq_data : ∀ (bs : ByteArray), bs.toList = bs.data.toList
  | ⟨⟨xs⟩⟩ => by
    have hloop : ∀ i r, ByteArray.toList.loop ⟨⟨xs⟩⟩ i r = r.reverse ++ xs.drop i := by
      intro i r
      fun_induction ByteArray.toList.loop ⟨⟨xs⟩⟩ i r with
      | case1 i r hi ih =>
        have hget : (ByteArray.mk ⟨xs⟩).get! i = xs[i] := getElem!_pos (⟨xs⟩ : Array UInt8) i hi
        rw [ih, hget, List.reverse_cons, List.append_assoc, List.singleton_append,
          List.drop_eq_getElem_cons hi]
      | case2 i r hni =>
        rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hni), List.append_nil]
    exact hloop 0 []

private theorem utf8_slash_length : (utf8 "/").length = 1 := by
  have hutf8 (s : String) :
      utf8 s = (s.toList.flatMap String.utf8EncodeChar).map (fun b => BitVec.ofNat 8 b.toNat) := by
    obtain ⟨l, rfl⟩ := s.exists_eq_ofList
    simp [utf8, List.utf8Encode, byteArray_toList_eq_data]
  rw [hutf8]
  rfl

private theorem pathOf_length_succ_le {dir name : List (BitVec 8)} {maxDir maxName : Nat}
    (hdir : dir.length ≤ maxDir) (hname : name.length ≤ maxName) :
    (pathOf dir name).length + 1 ≤ max (4 * maxDir + maxName + 16) 16 := by
  have hsl : (utf8 "/").length = 1 := utf8_slash_length
  unfold pathOf
  split
  · refine Nat.le_trans ?_ (Nat.le_max_left _ _)
    omega
  · simp only [List.length_append, hsl]
    refine Nat.le_trans ?_ (Nat.le_max_left _ _)
    omega

private theorem m5WriteStep_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {dir name : List (BitVec 8)} {maxDir maxName : Nat}
    (hdir_le : dir.length ≤ maxDir) (hname_le : name.length ≤ maxName) :
    let maxCap := max (4 * maxDir + maxName + 16) 16
    PhaseCreditSpec M (M5WriteStepEnv (dir, name))
      (10 * maxCap + 4 * 9539) 0 (3 * maxCap + 3 * 8195) maxCap := by
  intro maxCap
  unfold M5WriteStepEnv
  dsimp only
  by_cases hnil : dir = []
  · simp only [hnil, ↓reduceIte]
    have hnm_le : name.length + 1 ≤ maxCap := by
      refine Nat.le_trans ?_ (Nat.le_max_left (4 * maxDir + maxName + 16) 16)
      omega
    exact (phaseCredit_cliWriteFile hM name.length).mono
      (by omega) (Nat.le_refl 0) (by omega) hnm_le
  · simp only [hnil, ↓reduceIte]
    exact phaseCredit_m5LoopAEntry hM hnil hdir_le hname_le
      (pathOf_length_succ_le hdir_le hname_le)

theorem m5DirStep_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {dir : List (BitVec 8)} {names : List (List (BitVec 8))}
    {maxDir maxName : Nat}
    (hdir_le : dir.length ≤ maxDir)
    (hnames_le : ∀ nm ∈ names, nm.length ≤ maxName) :
    PhaseCreditSpec M (M5DirStepEnv dir names)
      (m5DirStepDeltaCum names.length maxDir maxName)
      0
      (m5DirStepDeltaPeak maxDir maxName)
      (m5DirStepMaxReq maxDir maxName) := by
  unfold M5DirStepEnv m5DirStepDeltaCum m5DirStepDeltaPeak m5DirStepMaxReq
  dsimp only
  have hit := PhaseCreditSpec.iter_zero_live (M := M)
    (Step := fun name => M5WriteStepEnv (dir, name))
    (c := 10 * max (4 * maxDir + maxName + 16) 16 + 4 * 9539)
    (p := 3 * max (4 * maxDir + maxName + 16) 16 + 3 * 8195)
    (r := max (4 * maxDir + maxName + 16) 16)
    names
    (fun nm hnm => m5WriteStep_phaseCredit hM hdir_le (hnames_le nm hnm))
  refine (hit.seq (PhaseCreditSpec.freeOnly hM.freeNonInc)).mono ?_ ?_ ?_ ?_
  · exact Nat.le_of_eq (Nat.add_zero _)
  · exact Nat.le_refl 0
  · rw [Nat.zero_add]
    exact Nat.max_le.mpr ⟨Nat.le_refl _, Nat.zero_le _⟩
  · exact Nat.max_le.mpr ⟨Nat.le_refl _, Nat.zero_le _⟩

def m6DeltaCum : Nat := 2 * 1024 + 9539
def m6DeltaLive : Nat := 1024 + 8195
def m6DeltaPeak : Nat := 1024 + 8195

theorem m6_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (ok : Bool) :
    PhaseCreditSpec M (M6Env ok) m6DeltaCum m6DeltaLive m6DeltaPeak 1024 := by
  unfold M6Env m6DeltaCum m6DeltaLive m6DeltaPeak
  have h1 : PhaseCreditSpec M (if ok then CliWriteStdoutEnv else (· = []))
      (2 * 1024 + 9539) (1024 + 8195) (1024 + 8195) 1024 := by
    cases ok
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact (PhaseCreditSpec.nil M).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    · simp only [↓reduceIte]
      exact phaseCredit_cliWriteStdout hM
  refine (h1.seq (PhaseCreditSpec.freeOnly hM.freeNonInc)).mono ?_ ?_ ?_ ?_
  · exact Nat.le_of_eq (Nat.add_zero _)
  · exact Nat.le_of_eq (Nat.add_zero _)
  · rw [Nat.add_zero]
    exact Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩
  · exact Nat.max_le.mpr ⟨Nat.le_refl _, Nat.zero_le _⟩

/-! ## Whole-`main` `CliMainEnv` Composition (`M1 → M2 → M3 → M4 → M5 → M6`) -/

def CliMainSetupEnv (uuidParse : UuidParser) (i : Inputs)
    (addrOpt : Option AddressCall) (needStdin : Bool)
    (evs : List AllocEvent) : Prop :=
  SeqEnv (M1PhaseEnv i.argv.length)
    (SeqEnv (M2CollectEnv i.argv.length)
      (SeqEnv
        (match addrOpt with
         | none => (· = [])
         | some ag => AddressEnv uuidParse ag)
        (M3PhaseEnv needStdin i.stdin (initFsState (cliInputs i)).files (utf8 "coins"))))
    evs

/-- Full real-order `main` allocator envelope (`M1..M3 → RunEnv g → M5 → M6`), including early-exit
prefix paths (`evs = []` or setup + `FreeOnlyEvs`). -/
def CliMainEnv (uuidParse : UuidParser) (RunEnv : RunCall → List AllocEvent → Prop)
    (g : RunCall) (addrOpt : Option AddressCall) (needStdin : Bool)
    (dirs : List (List (BitVec 8) × List (List (BitVec 8)))) (ok : Bool)
    (evs : List AllocEvent) : Prop :=
  SeqEnv (CliMainSetupEnv uuidParse g.i addrOpt needStdin)
    (fun evs' =>
      FreeOnlyEvs evs' ∨
      SeqEnv (RunEnv g) (SeqEnv (M5PhaseEnv dirs) (M6Env ok)) evs')
    evs

def cliMainDeltaCum (stdinCap fileCap runCum numDirty maxDir maxName : Nat) : Nat :=
  16 * 3 * 8 + m3PhaseDeltaCum stdinCap fileCap + runCum +
    numDirty * (10 * max (4 * maxDir + maxName + 16) 16 + 4 * 9539) + m6DeltaCum + 131072

def cliMainDeltaLive (stdinCap fileCap runLive : Nat) : Nat :=
  m3PhaseDeltaLive stdinCap fileCap + runLive + m6DeltaLive + 65536

def cliMainDeltaPeak (stdinCap fileCap runLive runPeak maxDir maxName : Nat) : Nat :=
  m3PhaseDeltaPeak stdinCap fileCap +
    max runPeak (runLive + max (m5DirStepDeltaPeak maxDir maxName) m6DeltaPeak) + 65536

def cliMainMaxReq (stdinCap fileCap runMaxReq maxDir maxName : Nat) : Nat :=
  max (m3PhaseMaxReq stdinCap fileCap) (max runMaxReq (max 1024 (m5DirStepMaxReq maxDir maxName)))

private theorem m5Phase_credit_priv {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M)
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))}
    {maxDir maxName : Nat}
    (hdirs : ∀ dn ∈ dirs, dn.1.length ≤ maxDir ∧ ∀ nm ∈ dn.2, nm.length ≤ maxName) :
    PhaseCreditSpec M (M5PhaseEnv dirs)
      (((dirs.map (fun dn => dn.2.length)).sum) *
        (10 * max (4 * maxDir + maxName + 16) 16 + 4 * 9539))
      0
      (m5DirStepDeltaPeak maxDir maxName)
      (m5DirStepMaxReq maxDir maxName) := by
  unfold M5PhaseEnv
  have hit : PhaseCreditSpec M
      (IterSeqEnv (fun dn => M5DirStepEnv dn.1 dn.2) dirs)
      (((dirs.map (fun dn => dn.2.length)).sum) *
        (10 * max (4 * maxDir + maxName + 16) 16 + 4 * 9539))
      0
      (m5DirStepDeltaPeak maxDir maxName)
      (m5DirStepMaxReq maxDir maxName) := by
    induction dirs with
    | nil =>
      exact (PhaseCreditSpec.nil M).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    | cons dn dns ih =>
      obtain ⟨hd1, hd2⟩ := hdirs dn List.mem_cons_self
      have hhd := m5DirStep_phaseCredit hM hd1 hd2
      have htl := ih (fun d hd => hdirs d (List.mem_cons_of_mem dn hd))
      refine (hhd.seq htl).mono ?_ (Nat.le_refl 0) ?_ ?_
      · have heq :
            dn.2.length * (10 * max (4 * maxDir + maxName + 16) 16 + 4 * 9539) +
              ((dns.map (fun d => d.2.length)).sum) *
                (10 * max (4 * maxDir + maxName + 16) 16 + 4 * 9539) =
            (((dn :: dns).map (fun d => d.2.length)).sum) *
              (10 * max (4 * maxDir + maxName + 16) 16 + 4 * 9539) := by
          simp only [List.map_cons, List.sum_cons, Nat.add_mul]
        exact Nat.le_of_eq heq
      · rw [Nat.zero_add]
        exact Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩
      · exact Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩
  refine (hit.seq (PhaseCreditSpec.freeOnly hM.freeNonInc)).mono ?_ ?_ ?_ ?_
  · exact Nat.le_of_eq (Nat.add_zero _)
  · exact Nat.le_refl 0
  · rw [Nat.zero_add]
    exact Nat.max_le.mpr ⟨Nat.le_refl _, Nat.zero_le _⟩
  · exact Nat.max_le.mpr ⟨Nat.le_refl _, Nat.zero_le _⟩

private theorem m3Live_le_peak_priv (stdinCap fileCap : Nat) :
    m3PhaseDeltaLive stdinCap fileCap ≤ m3PhaseDeltaPeak stdinCap fileCap := by
  unfold m3PhaseDeltaLive m3PhaseDeltaPeak
  refine Nat.le_trans ?_ (Nat.le_max_right _ _)
  refine Nat.add_le_add_left ?_ _
  have h2m : 2097152 + 8195 ≤ 3162118 := by decide
  exact Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans h2m (Nat.le_max_right _ _)⟩

private theorem addrOpt_credit_priv {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (uuidParse : UuidParser) (addrOpt : Option AddressCall) :
    PhaseCreditSpec M
      (match addrOpt with | none => (· = []) | some ag => AddressEnv uuidParse ag)
      9619 8235 8235 40 := by
  cases addrOpt with
  | none =>
    exact (PhaseCreditSpec.nil M).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  | some ag =>
    exact phaseCredit_address_cap40 hM uuidParse ag

private theorem setup_seq_priv {M : AllocCostModel} [HasFineReallocCredit M]
    {E₁ E₂ E₃ E₄ : List AllocEvent → Prop}
    {l₁ p₁ l₂ p₂ l₃ p₃ sL sP c₄ l₄ p₄ r₄ : Nat}
    (h₁ : PhaseCreditSpec M E₁ 9635 l₁ p₁ 48)
    (h₂ : PhaseCreditSpec M E₂ 29001 l₂ p₂ 64)
    (h₃ : PhaseCreditSpec M E₃ 9619 l₃ p₃ 40)
    (h₄ : PhaseCreditSpec M E₄ c₄ l₄ p₄ r₄)
    (hl : l₁ + (l₂ + l₃) ≤ sL)
    (hp : max p₁ (l₁ + max p₂ (l₂ + p₃)) ≤ sP)
    (hlp : sL ≤ sP) :
    PhaseCreditSpec M (SeqEnv E₁ (SeqEnv E₂ (SeqEnv E₃ E₄)))
      (48255 + c₄) (sL + l₄) (sP + p₄) (max 64 r₄) := by
  have h₃₄ := h₃.seq h₄
  have h₂₃₄ := h₂.seq h₃₄
  have h₁₂₃₄ := h₁.seq h₂₃₄
  exact h₁₂₃₄.mono (by omega) (by omega) (by omega) (by omega)

private theorem cliMainSetup_credit_priv {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (uuidParse : UuidParser) {i : Inputs} {stdinCap fileCap : Nat}
    (hcaps : CliPqDomainCaps stdinCap fileCap i)
    (addrOpt : Option AddressCall) (needStdin : Bool) :
    PhaseCreditSpec M (CliMainSetupEnv uuidParse i addrOpt needStdin)
      (48255 + m3PhaseDeltaCum stdinCap fileCap)
      (41255 + m3PhaseDeltaLive stdinCap fileCap)
      (41279 + m3PhaseDeltaPeak stdinCap fileCap)
      (max 64 (m3PhaseMaxReq stdinCap fileCap)) := by
  unfold CliMainSetupEnv
  have hm1 : PhaseCreditSpec M (M1PhaseEnv i.argv.length) 9635 8243 8243 48 :=
    phaseCredit_m1Phase hM hcaps.argv_le
  have hm2 : PhaseCreditSpec M (M2CollectEnv i.argv.length) 29001 24777 33036 64 :=
    phaseCredit_m2Collect hM hcaps.argv_le
  have had := addrOpt_credit_priv hM uuidParse addrOpt
  have hm3 := m3Phase_phaseCredit hM needStdin i.stdin
    (initFsState (cliInputs i)).files (utf8 "coins") hcaps.stdin_le hcaps.files_bounded
  exact setup_seq_priv hm1 hm2 had hm3 (by decide) (by decide) (by decide)

private theorem cliMainTail_credit_priv {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {RunEnv : RunCall → List AllocEvent → Prop} {g : RunCall}
    {runCum runLive runPeak runMaxReq maxDir maxName : Nat}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    (hdirs : ∀ dn ∈ dirs, dn.1.length ≤ maxDir ∧ ∀ nm ∈ dn.2, nm.length ≤ maxName)
    (hrun : PhaseCreditSpec M (RunEnv g) runCum runLive runPeak runMaxReq) :
    PhaseCreditSpec M
      (fun evs' =>
        FreeOnlyEvs evs' ∨ SeqEnv (RunEnv g) (SeqEnv (M5PhaseEnv dirs) (M6Env ok)) evs')
      (runCum +
        (((dirs.map (fun dn => dn.2.length)).sum) *
          (10 * max (4 * maxDir + maxName + 16) 16 + 4 * 9539) + m6DeltaCum))
      (runLive + m6DeltaLive)
      (max runPeak (runLive + max (m5DirStepDeltaPeak maxDir maxName) m6DeltaPeak))
      (max runMaxReq (max 1024 (m5DirStepMaxReq maxDir maxName))) := by
  have hm56 : PhaseCreditSpec M (SeqEnv (M5PhaseEnv dirs) (M6Env ok))
      (((dirs.map (fun dn => dn.2.length)).sum) *
        (10 * max (4 * maxDir + maxName + 16) 16 + 4 * 9539) + m6DeltaCum)
      m6DeltaLive
      (max (m5DirStepDeltaPeak maxDir maxName) m6DeltaPeak)
      (max 1024 (m5DirStepMaxReq maxDir maxName)) := by
    refine ((m5Phase_credit_priv hM hdirs).seq (m6_phaseCredit hM ok)).mono ?_ ?_ ?_ ?_
    · exact Nat.le_refl _
    · exact Nat.le_of_eq (Nat.zero_add _)
    · exact Nat.le_of_eq (congrArg (max _) (Nat.zero_add _))
    · exact Nat.le_of_eq (Nat.max_comm _ _)
  have h456 := hrun.seq hm56
  refine ((PhaseCreditSpec.freeOnly hM.freeNonInc).or h456).mono ?_ ?_ ?_ ?_
  · exact Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩
  · exact Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩
  · exact Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩
  · exact Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩

private theorem cliMain_combine_priv {M : AllocCostModel} [HasFineReallocCredit M]
    {ESetup ETail : List AllocEvent → Prop}
    {m3Cum m3Live m3Peak m3Req sL sP livePad : Nat}
    {runCum runLive pTail runMaxReq m5Cum m5Req m6Cum m6Live : Nat}
    (hSetup : PhaseCreditSpec M ESetup (48255 + m3Cum) (sL + m3Live) (sP + m3Peak) (max 64 m3Req))
    (hTail : PhaseCreditSpec M ETail
      (runCum + (m5Cum + m6Cum)) (runLive + m6Live) pTail (max runMaxReq (max 1024 m5Req)))
    (hm3 : m3Live ≤ m3Peak)
    (hs_lp : sL ≤ sP)
    (hs_p : sP ≤ 65536)
    (hs_l : sL ≤ livePad) :
    PhaseCreditSpec M (SeqEnv ESetup ETail)
      (16 * 3 * 8 + m3Cum + runCum + m5Cum + m6Cum + 131072)
      (m3Live + runLive + m6Live + livePad)
      (m3Peak + pTail + 65536)
      (max m3Req (max runMaxReq (max 1024 m5Req))) :=
  (hSetup.seq hTail).mono (by omega) (by omega) (by omega) (by omega)

theorem cliMain_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {uuidParse : UuidParser} {RunEnv : RunCall → List AllocEvent → Prop}
    {g : RunCall} {stdinCap fileCap runCum runLive runPeak runMaxReq maxDir maxName : Nat}
    {addrOpt : Option AddressCall} {needStdin : Bool}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    (hcaps : CliPqDomainCaps stdinCap fileCap g.i)
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ 64)
    (hdirs : ∀ dn ∈ dirs, dn.1.length ≤ maxDir ∧ ∀ nm ∈ dn.2, nm.length ≤ maxName)
    (hrun : PhaseCreditSpec M (RunEnv g) runCum runLive runPeak runMaxReq) :
    PhaseCreditSpec M (CliMainEnv uuidParse RunEnv g addrOpt needStdin dirs ok)
      (cliMainDeltaCum stdinCap fileCap runCum ((dirs.map (fun dn => dn.2.length)).sum) maxDir maxName)
      (cliMainDeltaLive stdinCap fileCap runLive)
      (cliMainDeltaPeak stdinCap fileCap runLive runPeak maxDir maxName)
      (cliMainMaxReq stdinCap fileCap runMaxReq maxDir maxName) := by
  let _ := haddr
  unfold CliMainEnv cliMainDeltaCum cliMainDeltaLive cliMainDeltaPeak cliMainMaxReq
  exact cliMain_combine_priv
    (cliMainSetup_credit_priv hM uuidParse hcaps addrOpt needStdin)
    (cliMainTail_credit_priv hM hdirs hrun)
    (m3Live_le_peak_priv stdinCap fileCap)
    (by decide) (by decide) (by decide)

/-! ## Tight Whole-`main` Bounds (`131072 ≤ smallMaxReq M < 262144`) -/

/-- `CliIo` doubling-schedule setup envelope (`M1 → M2Collect → address → M3PhaseCliIoEnv`). -/
def CliMainSetupCliIoEnv (uuidParse : UuidParser) (argvLen : Nat)
    (addrOpt : Option AddressCall) (needStdin : Bool) (stdinLen fileLen : Nat)
    (evs : List AllocEvent) : Prop :=
  SeqEnv (M1PhaseEnv argvLen)
    (SeqEnv (M2CollectEnv argvLen)
      (SeqEnv
        (match addrOpt with
         | none => (· = [])
         | some ag => AddressEnv uuidParse ag)
        (M3PhaseCliIoEnv needStdin stdinLen fileLen)))
    evs

/-- Full real-order `main` allocator envelope with `CliIo` doubling `M3PhaseCliIoEnv`. -/
def CliMainCliIoEnv (uuidParse : UuidParser) (RunEnv : RunCall → List AllocEvent → Prop)
    (g : RunCall) (addrOpt : Option AddressCall) (needStdin : Bool) (stdinLen fileLen : Nat)
    (dirs : List (List (BitVec 8) × List (List (BitVec 8)))) (ok : Bool)
    (evs : List AllocEvent) : Prop :=
  SeqEnv (CliMainSetupCliIoEnv uuidParse g.i.argv.length addrOpt needStdin stdinLen fileLen)
    (fun evs' =>
      FreeOnlyEvs evs' ∨
      SeqEnv (RunEnv g) (SeqEnv (M5PhaseEnv dirs) (M6Env ok)) evs')
    evs

/-- Tight whole-`main` `cumSmall` bound (`m3PhaseDeltaCum_tight = 1,147,514` B plus `48,255` B for M1/M2). -/
def cliMainDeltaCum_tight (runCum numDirty maxDir maxName : Nat) : Nat :=
  48255 + m3PhaseDeltaCum_tight + runCum +
    numDirty * (10 * max (4 * maxDir + maxName + 16) 16 + 4 * 9539) + m6DeltaCum

/-- Tight whole-`main` `liveLarge` bound (`64, 1024 ≤ smallMaxReq M`, so M1/M2/M6 have `Δlive = 0`). -/
def cliMainDeltaLive_tight (stdinCap fileCap runLive : Nat) : Nat :=
  m3PhaseDeltaLive stdinCap fileCap + runLive

/-- Tight whole-`main` `peakLarge` bound (`max m3Peak (m3Live + pTail)` with M1/M2/M6 `Δpeak = 0`). -/
def cliMainDeltaPeak_tight (stdinCap fileCap runLive runPeak maxDir maxName : Nat) : Nat :=
  max (m3PhaseDeltaPeak stdinCap fileCap)
    (m3PhaseDeltaLive stdinCap fileCap + max runPeak (runLive + m5DirStepDeltaPeak maxDir maxName))

/-- Small-regime `M6Env` `PhaseCreditSpec` (`Δlive = 0`, `Δpeak = 0`) when `1024 ≤ smallMaxReq M`. -/
theorem m6_phaseCredit_small1024 {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsm1024 : 1024 ≤ HasFineReallocCredit.smallMaxReq M) (ok : Bool) :
    PhaseCreditSpec M (M6Env ok) m6DeltaCum 0 0 1024 := by
  unfold M6Env m6DeltaCum
  have h1 : PhaseCreditSpec M (if ok then CliWriteStdoutEnv else (· = []))
      (2 * 1024 + 9539) 0 0 1024 := by
    cases ok
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact (PhaseCreditSpec.nil M).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    · simp only [↓reduceIte]
      exact phaseCredit_cliWriteStdout_small1024 hM hsm1024
  refine (h1.seq (PhaseCreditSpec.freeOnly hM.freeNonInc)).mono ?_ ?_ ?_ ?_
  · exact Nat.le_of_eq (Nat.add_zero _)
  · exact Nat.le_refl 0
  · exact Nat.le_refl 0
  · exact Nat.max_le.mpr ⟨Nat.le_refl _, Nat.zero_le _⟩

private theorem addrOpt_credit_small64_priv {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsm64 : 64 ≤ HasFineReallocCredit.smallMaxReq M)
    (uuidParse : UuidParser) (addrOpt : Option AddressCall) :
    PhaseCreditSpec M
      (match addrOpt with | none => (· = []) | some ag => AddressEnv uuidParse ag)
      9619 0 0 40 := by
  cases addrOpt with
  | none =>
    exact (PhaseCreditSpec.nil M).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  | some ag =>
    exact phaseCredit_address_small64 hM hsm64 uuidParse ag

private theorem cliMainSetup_credit_tight_priv {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M)
    (hSmLo : 131072 ≤ HasFineReallocCredit.smallMaxReq M)
    (hSmHi : HasFineReallocCredit.smallMaxReq M < 262144)
    (uuidParse : UuidParser) {i : Inputs} {stdinCap fileCap : Nat}
    (hcaps : CliPqDomainCaps stdinCap fileCap i)
    (addrOpt : Option AddressCall) (needStdin : Bool) :
    PhaseCreditSpec M (CliMainSetupEnv uuidParse i addrOpt needStdin)
      (48255 + m3PhaseDeltaCum_tight)
      (0 + m3PhaseDeltaLive stdinCap fileCap)
      (0 + m3PhaseDeltaPeak stdinCap fileCap)
      (max 64 (m3PhaseMaxReq stdinCap fileCap)) := by
  have hsm64 : 64 ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans (by decide) hSmLo
  unfold CliMainSetupEnv
  have hm1 : PhaseCreditSpec M (M1PhaseEnv i.argv.length) 9635 0 0 48 :=
    phaseCredit_m1Phase_small64 hM hsm64 hcaps.argv_le
  have hm2 : PhaseCreditSpec M (M2CollectEnv i.argv.length) 29001 0 0 64 :=
    phaseCredit_m2Collect_small64 hM hsm64 hcaps.argv_le
  have had := addrOpt_credit_small64_priv hM hsm64 uuidParse addrOpt
  have hm3 := m3Phase_phaseCredit_tight hM hSmLo hSmHi needStdin i.stdin
    (initFsState (cliInputs i)).files (utf8 "coins") hcaps.stdin_le hcaps.files_bounded
  exact setup_seq_priv hm1 hm2 had hm3 (by decide) (by decide) (by decide)

private theorem cliMainSetup_cliIo_credit_tight_priv {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M)
    (hSmLo : 131072 ≤ HasFineReallocCredit.smallMaxReq M)
    (hSmHi : HasFineReallocCredit.smallMaxReq M < 262144)
    (uuidParse : UuidParser) {argvLen : Nat} (hargv : argvLen ≤ 3)
    (addrOpt : Option AddressCall) (needStdin : Bool) (stdinLen fileLen : Nat) :
    PhaseCreditSpec M (CliMainSetupCliIoEnv uuidParse argvLen addrOpt needStdin stdinLen fileLen)
      (48255 + m3PhaseDeltaCum_tight)
      (0 + m3PhaseDeltaLive 1048576 2097152)
      (0 + m3PhaseDeltaPeak 1048576 2097152)
      (max 64 (m3PhaseMaxReq 1048576 2097152)) := by
  have hsm64 : 64 ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans (by decide) hSmLo
  unfold CliMainSetupCliIoEnv
  have hm1 : PhaseCreditSpec M (M1PhaseEnv argvLen) 9635 0 0 48 :=
    phaseCredit_m1Phase_small64 hM hsm64 hargv
  have hm2 : PhaseCreditSpec M (M2CollectEnv argvLen) 29001 0 0 64 :=
    phaseCredit_m2Collect_small64 hM hsm64 hargv
  have had := addrOpt_credit_small64_priv hM hsm64 uuidParse addrOpt
  have hm3 := m3Phase_cliIo_phaseCredit_tight hM hSmLo hSmHi needStdin stdinLen fileLen
  exact setup_seq_priv hm1 hm2 had hm3 (by decide) (by decide) (by decide)

private theorem cliMainTail_credit_tight_priv {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsm1024 : 1024 ≤ HasFineReallocCredit.smallMaxReq M)
    {RunEnv : RunCall → List AllocEvent → Prop} {g : RunCall}
    {runCum runLive runPeak runMaxReq maxDir maxName : Nat}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    (hdirs : ∀ dn ∈ dirs, dn.1.length ≤ maxDir ∧ ∀ nm ∈ dn.2, nm.length ≤ maxName)
    (hrun : PhaseCreditSpec M (RunEnv g) runCum runLive runPeak runMaxReq) :
    PhaseCreditSpec M
      (fun evs' =>
        FreeOnlyEvs evs' ∨ SeqEnv (RunEnv g) (SeqEnv (M5PhaseEnv dirs) (M6Env ok)) evs')
      (runCum +
        (((dirs.map (fun dn => dn.2.length)).sum) *
          (10 * max (4 * maxDir + maxName + 16) 16 + 4 * 9539) + m6DeltaCum))
      runLive
      (max runPeak (runLive + m5DirStepDeltaPeak maxDir maxName))
      (max runMaxReq (max 1024 (m5DirStepMaxReq maxDir maxName))) := by
  have hm56 : PhaseCreditSpec M (SeqEnv (M5PhaseEnv dirs) (M6Env ok))
      (((dirs.map (fun dn => dn.2.length)).sum) *
        (10 * max (4 * maxDir + maxName + 16) 16 + 4 * 9539) + m6DeltaCum)
      0
      (m5DirStepDeltaPeak maxDir maxName)
      (max 1024 (m5DirStepMaxReq maxDir maxName)) := by
    refine ((m5Phase_credit_priv hM hdirs).seq (m6_phaseCredit_small1024 hM hsm1024 ok)).mono
      ?_ ?_ ?_ ?_
    · exact Nat.le_refl _
    · exact Nat.le_refl 0
    · rw [Nat.zero_add]
      exact Nat.max_le.mpr ⟨Nat.le_refl _, Nat.zero_le _⟩
    · exact Nat.le_of_eq (Nat.max_comm _ _)
  have h456 := hrun.seq hm56
  refine ((PhaseCreditSpec.freeOnly hM.freeNonInc).or h456).mono ?_ ?_ ?_ ?_
  · exact Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩
  · rw [Nat.add_zero]
    exact Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩
  · exact Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩
  · exact Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩

private theorem cliMain_combine_tight_priv {M : AllocCostModel} [HasFineReallocCredit M]
    {ESetup ETail : List AllocEvent → Prop}
    {m3Cum m3Live m3Peak m3Req : Nat}
    {runCum runLive pTail runMaxReq m5Cum m5Req m6Cum : Nat}
    (hSetup : PhaseCreditSpec M ESetup (48255 + m3Cum) (0 + m3Live) (0 + m3Peak) (max 64 m3Req))
    (hTail : PhaseCreditSpec M ETail
      (runCum + (m5Cum + m6Cum)) runLive pTail (max runMaxReq (max 1024 m5Req))) :
    PhaseCreditSpec M (SeqEnv ESetup ETail)
      (48255 + m3Cum + runCum + m5Cum + m6Cum)
      (m3Live + runLive)
      (max m3Peak (m3Live + pTail))
      (max m3Req (max runMaxReq (max 1024 m5Req))) :=
  (hSetup.seq hTail).mono (by omega) (by omega) (by omega) (by omega)

/-- Tight full real-order `CliMainEnv` `PhaseCreditSpec` when `131072 ≤ smallMaxReq M < 262144`. -/
theorem cliMain_phaseCredit_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M)
    (hSmLo : 131072 ≤ HasFineReallocCredit.smallMaxReq M)
    (hSmHi : HasFineReallocCredit.smallMaxReq M < 262144)
    {uuidParse : UuidParser} {RunEnv : RunCall → List AllocEvent → Prop}
    {g : RunCall} {stdinCap fileCap runCum runLive runPeak runMaxReq maxDir maxName : Nat}
    {addrOpt : Option AddressCall} {needStdin : Bool}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    (hcaps : CliPqDomainCaps stdinCap fileCap g.i)
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ 64)
    (hdirs : ∀ dn ∈ dirs, dn.1.length ≤ maxDir ∧ ∀ nm ∈ dn.2, nm.length ≤ maxName)
    (hrun : PhaseCreditSpec M (RunEnv g) runCum runLive runPeak runMaxReq) :
    PhaseCreditSpec M (CliMainEnv uuidParse RunEnv g addrOpt needStdin dirs ok)
      (cliMainDeltaCum_tight runCum ((dirs.map (fun dn => dn.2.length)).sum) maxDir maxName)
      (cliMainDeltaLive_tight stdinCap fileCap runLive)
      (cliMainDeltaPeak_tight stdinCap fileCap runLive runPeak maxDir maxName)
      (cliMainMaxReq stdinCap fileCap runMaxReq maxDir maxName) := by
  let _ := haddr
  have hsm1024 : 1024 ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans (by decide) hSmLo
  unfold CliMainEnv cliMainDeltaCum_tight cliMainDeltaLive_tight cliMainDeltaPeak_tight cliMainMaxReq
  exact cliMain_combine_tight_priv
    (cliMainSetup_credit_tight_priv hM hSmLo hSmHi uuidParse hcaps addrOpt needStdin)
    (cliMainTail_credit_tight_priv hM hsm1024 hdirs hrun)

theorem cliMain_phaseCredit_fine
    (hM : ModelHyps fineCostModel)
    {uuidParse : UuidParser} {RunEnv : RunCall → List AllocEvent → Prop}
    {g : RunCall} {stdinCap fileCap runCum runLive runPeak runMaxReq maxDir maxName : Nat}
    {addrOpt : Option AddressCall} {needStdin : Bool}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    (hcaps : CliPqDomainCaps stdinCap fileCap g.i)
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ 64)
    (hdirs : ∀ dn ∈ dirs, dn.1.length ≤ maxDir ∧ ∀ nm ∈ dn.2, nm.length ≤ maxName)
    (hrun : PhaseCreditSpec fineCostModel (RunEnv g) runCum runLive runPeak runMaxReq) :
    PhaseCreditSpec fineCostModel (CliMainEnv uuidParse RunEnv g addrOpt needStdin dirs ok)
      (cliMainDeltaCum_tight runCum ((dirs.map (fun dn => dn.2.length)).sum) maxDir maxName)
      (cliMainDeltaLive_tight stdinCap fileCap runLive)
      (cliMainDeltaPeak_tight stdinCap fileCap runLive runPeak maxDir maxName)
      (cliMainMaxReq stdinCap fileCap runMaxReq maxDir maxName) :=
  cliMain_phaseCredit_tight hM
    (by rw [fineCostModel_smallMaxReq_eq]; decide)
    (by rw [fineCostModel_smallMaxReq_eq]; decide)
    hcaps haddr hdirs hrun

/-- Tight full real-order `CliMainCliIoEnv` `PhaseCreditSpec` (`j = 8` `read_stdin` + `j = 9`
`read_file` doubling schedules, `Δcum = 1,147,514` B in M3) when `131072 ≤ smallMaxReq M < 262144`. -/
theorem cliMain_cliIo_phaseCredit_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M)
    (hSmLo : 131072 ≤ HasFineReallocCredit.smallMaxReq M)
    (hSmHi : HasFineReallocCredit.smallMaxReq M < 262144)
    {uuidParse : UuidParser} {RunEnv : RunCall → List AllocEvent → Prop}
    {g : RunCall} {stdinCap fileCap runCum runLive runPeak runMaxReq maxDir maxName : Nat}
    {addrOpt : Option AddressCall} {needStdin : Bool} {stdinLen fileLen : Nat}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    (hcaps : CliPqDomainCaps stdinCap fileCap g.i)
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ 64)
    (hdirs : ∀ dn ∈ dirs, dn.1.length ≤ maxDir ∧ ∀ nm ∈ dn.2, nm.length ≤ maxName)
    (hrun : PhaseCreditSpec M (RunEnv g) runCum runLive runPeak runMaxReq) :
    PhaseCreditSpec M
      (CliMainCliIoEnv uuidParse RunEnv g addrOpt needStdin stdinLen fileLen dirs ok)
      (cliMainDeltaCum_tight runCum ((dirs.map (fun dn => dn.2.length)).sum) maxDir maxName)
      (cliMainDeltaLive_tight 1048576 2097152 runLive)
      (cliMainDeltaPeak_tight 1048576 2097152 runLive runPeak maxDir maxName)
      (cliMainMaxReq 1048576 2097152 runMaxReq maxDir maxName) := by
  let _ := haddr
  have hsm1024 : 1024 ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans (by decide) hSmLo
  unfold CliMainCliIoEnv cliMainDeltaCum_tight cliMainDeltaLive_tight cliMainDeltaPeak_tight cliMainMaxReq
  exact cliMain_combine_tight_priv
    (cliMainSetup_cliIo_credit_tight_priv hM hSmLo hSmHi uuidParse hcaps.argv_le
      addrOpt needStdin stdinLen fileLen)
    (cliMainTail_credit_tight_priv hM hsm1024 hdirs hrun)

theorem cliMain_cliIo_phaseCredit_fine
    (hM : ModelHyps fineCostModel)
    {uuidParse : UuidParser} {RunEnv : RunCall → List AllocEvent → Prop}
    {g : RunCall} {stdinCap fileCap runCum runLive runPeak runMaxReq maxDir maxName : Nat}
    {addrOpt : Option AddressCall} {needStdin : Bool} {stdinLen fileLen : Nat}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    (hcaps : CliPqDomainCaps stdinCap fileCap g.i)
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ 64)
    (hdirs : ∀ dn ∈ dirs, dn.1.length ≤ maxDir ∧ ∀ nm ∈ dn.2, nm.length ≤ maxName)
    (hrun : PhaseCreditSpec fineCostModel (RunEnv g) runCum runLive runPeak runMaxReq) :
    PhaseCreditSpec fineCostModel
      (CliMainCliIoEnv uuidParse RunEnv g addrOpt needStdin stdinLen fileLen dirs ok)
      (cliMainDeltaCum_tight runCum ((dirs.map (fun dn => dn.2.length)).sum) maxDir maxName)
      (cliMainDeltaLive_tight 1048576 2097152 runLive)
      (cliMainDeltaPeak_tight 1048576 2097152 runLive runPeak maxDir maxName)
      (cliMainMaxReq 1048576 2097152 runMaxReq maxDir maxName) :=
  cliMain_cliIo_phaseCredit_tight hM
    (by rw [fineCostModel_smallMaxReq_eq]; decide)
    (by rw [fineCostModel_smallMaxReq_eq]; decide)
    hcaps haddr hdirs hrun

end LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec
