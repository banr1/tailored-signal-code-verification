/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.PeakBudget.DirPeakHelpers
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget

/-!
# CLI `main` I/O, Callee, and M1–M6 Credit Helpers

`PhaseCreditSpec` bounds for `Cli.main` callees (`address`, `reserve16`, `try_allocate_in`),
M1 (`argv`), M2 (`M2CollectEnv` + `address`), M3 (`read_stdin` + `"coins"` `read_file`),
M5 (`M5LoopAEntryEnv` with `Δlive = 0` via `sc = 63` deallocation cancellation), and
M6 (`1024`-B `LineWriter` `write_stdout`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.CliMainIoCredit

open Arm64 (FsEntry)
open CryptoVerification.E2E.Pqxdh.Shared (TryAllocateInCall)
open CryptoVerification.LibsignalTripleRatchet (reserveCap)
open CryptoVerification.LibsignalTripleRatchetRepr
  (UuidParser hyphenatedLength pniPrefix pniPrefix_word serviceIdParse tryParseHyphenated)
open CryptoVerification.SignalSession.CliExt (blockingAncestorF pathStr readFileResult readViewF)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV AddressCall Reserve16Call addrParse parseUnsigned rsplitDot)
open CryptoVerification.SpqrV1.Alloc (reserveCapStride reserveCapStride_one reserveMinCap)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv
   rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine.ClientBounds (eventStepAlign eventStepReq)
open LibsignalBinary.Heap.SpecBudget
  (ReadFileEnv ReadStdinEnv allocBytes1Events cliIoCapsEvents cliIoReadScheduleCaps)
open LibsignalBinary.Proofs.PeakBudget.DirPeakHelpers
  (cliIoCap cliIoCapEvents cliIoCapEventsGo cliIoCapEvents_readCaps_pos cliIoCapEvents_readCaps_zero
   cliIoCapIdx cliIoCapIdx_le cliIoCap_mono cliIoCap_pos cliIoReadCaps
   cliIoStepLiveBound cliIoStepPeakBound cliIoStepPeakBound_mono
   cliIoTightCumBound cliIoTightCumBound_eight cliIoTightCumBound_mono
   phaseCreditSpec_cliIoReadFile_tight phaseCreditSpec_cliIoReadFile_uncond
   req_align_cliIoReadCaps stepEvents_cliIoCapSeq_tight stepEvents_cliIoReadStdin_uncond)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (ConcatEnv DeallocCreditSpec IterSeqEnv ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget
  (AddressEnv Reserve16Env TryAllocateInEnv addressEvents reserve16Events tryAllocateInEvents)

/-! ## Single-Step Realloc and `allocBytes1Events` Credit Lemmas -/

/-- Affine `PhaseCreditSpec` for a standalone `rustReallocEvents old new al` (`al ≤ 16`, `al ≤ new`),
covering all four S/L quadrants (including `old = 0`) via `ModelHyps.step_nonFree_aff`. -/
theorem phaseCredit_rustRealloc_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {old new al : Nat} (hal : al ≤ 16) (hal_new : al ≤ new) :
    PhaseCreditSpec M (· = rustReallocEvents old new al)
      (2 * new + 9539) (new + 8195) (new + 8195) new where
  req_align _ h ev hev := by
    subst h
    unfold rustReallocEvents at hev
    simp only [hal, hal_new, and_self, ↓reduceIte, List.mem_singleton] at hev
    subst hev
    exact ⟨Nat.le_refl new, hal⟩
  credit_le st0 {_} h := by
    subst h
    unfold rustReallocEvents
    simp only [hal, hal_new, and_self, ↓reduceIte, AllocCostModel.stepEvents, List.foldl]
    exact hM.step_nonFree_aff (ev := .realloc al old new) (maxReq := new) st0
      (Nat.le_refl new) hal

/-- Small-quadrant `PhaseCreditSpec` for `rustReallocEvents old new al` including `old = 0` when
both `old` and `new` lie within `smallMaxReq M` (`Δlive = 0`, `Δpeak = 0`). -/
theorem phaseCredit_rustRealloc_small_any {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {old new al : Nat} (hal : al ≤ 16) (hal_new : al ≤ new)
    (hold : old ≤ HasFineReallocCredit.smallMaxReq M)
    (hnew : new ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (· = rustReallocEvents old new al)
      (2 * new + 9539) 0 0 new where
  req_align _ h ev hev := by
    subst h
    unfold rustReallocEvents at hev
    simp only [hal, hal_new, and_self, ↓reduceIte, List.mem_singleton] at hev
    subst hev
    exact ⟨Nat.le_refl new, hal⟩
  credit_le st0 {_} h := by
    subst h
    have hsr := hM.smallRealloc_le hnew
    unfold rustReallocEvents
    simp only [hal, hal_new, and_self, ↓reduceIte, AllocCostModel.stepEvents, List.foldl]
    obtain ⟨hc, hl, hp⟩ := hM.step_realloc_small_small_any st0 hal hold hnew
    omega

/-- Affine `PhaseCreditSpec` for `allocBytes1Events bs` (`bs.length ≤ cap`). -/
theorem phaseCredit_allocBytes1_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (bs : List (BitVec 8)) {cap : Nat} (hlen : bs.length ≤ cap) :
    PhaseCreditSpec M (· = allocBytes1Events bs)
      (2 * cap + 9539) (cap + 8195) (cap + 8195) cap := by
  unfold allocBytes1Events
  split
  · exact (PhaseCreditSpec.nil M).mono (by omega) (by omega) (by omega) (by omega)
  · exact (PhaseCreditSpec.rustAlloc_aff hM (req := bs.length) (al := 1) (by omega)).mono
      (by omega) (by omega) (by omega) hlen

/-! ## Callee Bounds (`address`, `reserve16`, `try_allocate_in`) -/

private theorem span_loop_snd_length_le {α : Type} (p : α → Bool) :
    ∀ (xs acc : List α), (List.span.loop p xs acc).2.length ≤ xs.length
  | [], acc => by simp [List.span.loop]
  | x :: xs, acc => by
    unfold List.span.loop
    split
    · exact Nat.le_trans (span_loop_snd_length_le p xs (x :: acc)) (Nat.le_succ _)
    · exact Nat.le_refl _

private theorem tryParseHyphenated_length_eq (uuidParse : UuidParser) {u} {bs : List (BitVec 8)}
    (h : tryParseHyphenated uuidParse bs = some u) :
    bs.length = 36 := by
  unfold tryParseHyphenated hyphenatedLength at h
  split_ifs at h with hlen
  exact hlen

private theorem serviceIdParse_length_le (uuidParse : UuidParser) {sid} {bs : List (BitVec 8)}
    (h : serviceIdParse uuidParse bs = some sid) :
    bs.length ≤ 40 := by
  unfold serviceIdParse at h
  have hpni : pniPrefix.length = 4 := by
    rw [pniPrefix_word]
    rfl
  split_ifs at h with hp
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨u, hu, _⟩ := h
    have hdrop := tryParseHyphenated_length_eq uuidParse hu
    have hpre := (List.isPrefixOf_iff_prefix.mp hp).length_le
    rw [List.length_drop, hpni] at hdrop
    rw [hpni] at hpre
    omega
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨u, hu, _⟩ := h
    have h36 := tryParseHyphenated_length_eq uuidParse hu
    omega

/-- Any `a` accepted by `addrParse uuidParse bs` (for *any* `uuidParse : UuidParser`) has
`a.name.length ≤ 40` and `a.name.length < bs.length`. -/
theorem addrParse_name_bounds (uuidParse : UuidParser) (bs : List (BitVec 8)) {a : AddrV}
    (h : addrParse uuidParse bs = some a) :
    a.name.length ≤ 40 ∧ a.name.length < bs.length := by
  unfold addrParse at h
  rcases hrs : rsplitDot bs with _ | ⟨name, dev⟩ <;> rw [hrs] at h
  · cases h
  · have hlt : name.length < bs.length := by
      unfold rsplitDot List.span at hrs
      cases hsp : List.span.loop (fun b => b != 46#8) bs.reverse [] with
      | mk devR rest =>
        rw [hsp] at hrs
        cases rest with
        | nil => cases hrs
        | cons dot nameR =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hrs
          rcases hrs with ⟨rfl, _⟩
          have h0 := span_loop_snd_length_le (fun b => b != 46#8) bs.reverse []
          rw [hsp] at h0
          simp only [List.length_cons, List.length_reverse] at h0 ⊢
          omega
    dsimp only at h
    rcases hsid : serviceIdParse uuidParse name with _ | sid <;> rw [hsid] at h
    · cases h
    · rcases hp : parseUnsigned 255 dev with _ | d <;> rw [hp] at h
      · cases h
      · dsimp only at h
        split_ifs at h
        injection h with ha
        rw [← ha]
        exact ⟨serviceIdParse_length_le uuidParse hsid, hlt⟩

/-- Affine `PhaseCreditSpec` for `AddressEnv uuidParse x`. -/
theorem phaseCredit_address {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (uuidParse : UuidParser) (x : AddressCall) :
    PhaseCreditSpec M (AddressEnv uuidParse x)
      (2 * x.bs.length + 28617) (x.bs.length + 8195)
      (x.bs.length + 16390) (max 48 x.bs.length) := by
  unfold AddressEnv addressEvents
  cases ha : addrParse uuidParse x.bs with
  | none =>
    exact (PhaseCreditSpec.nil M).mono (by omega) (by omega) (by omega) (by omega)
  | some a =>
    obtain ⟨_, hlt⟩ := addrParse_name_bounds uuidParse x.bs ha
    exact (PhaseCreditSpec.rustAlloc_aff hM (req := a.name.length) (al := 1) (by omega)).mono
      (by omega) (by omega) (by omega) (by omega)

/-- Tight `PhaseCreditSpec` for `AddressEnv uuidParse x` using `a.name.length ≤ 40` directly
(independent of `x.bs.length`). -/
theorem phaseCredit_address_cap40 {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (uuidParse : UuidParser) (x : AddressCall) :
    PhaseCreditSpec M (AddressEnv uuidParse x)
      (2 * 40 + 9539) (40 + 8195) (40 + 8195) 40 := by
  unfold AddressEnv addressEvents
  cases ha : addrParse uuidParse x.bs with
  | none =>
    exact (PhaseCreditSpec.nil M).mono (by omega) (by omega) (by omega) (by omega)
  | some a =>
    obtain ⟨hle40, _⟩ := addrParse_name_bounds uuidParse x.bs ha
    exact (PhaseCreditSpec.rustAlloc_aff hM (req := a.name.length) (al := 1) (by omega)).mono
      (by omega) (by omega) (by omega) hle40

/-- Small-regime `PhaseCreditSpec` for `AddressEnv uuidParse x` (`Δlive = 0`, `Δpeak = 0`) when
`64 ≤ smallMaxReq M`. -/
theorem phaseCredit_address_small64 {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsm64 : 64 ≤ HasFineReallocCredit.smallMaxReq M)
    (uuidParse : UuidParser) (x : AddressCall) :
    PhaseCreditSpec M (AddressEnv uuidParse x)
      (2 * 40 + 9539) 0 0 40 := by
  unfold AddressEnv addressEvents
  cases ha : addrParse uuidParse x.bs with
  | none =>
    exact (PhaseCreditSpec.nil M).mono (by omega) (by omega) (by omega) (by omega)
  | some a =>
    obtain ⟨hle40, _⟩ := addrParse_name_bounds uuidParse x.bs ha
    have hle : a.name.length ≤ HasFineReallocCredit.smallMaxReq M := by omega
    have hsa := hM.smallAlloc_le hle
    exact (PhaseCreditSpec.rustAlloc_small_any hM (req := a.name.length) (al := 1)
      (by omega) hle).mono (by omega) (Nat.le_refl 0) (Nat.le_refl 0) hle40

theorem reserveCapStride_16_ge_four (cap len add : Nat) :
    4 ≤ reserveCapStride 16 cap len add := by
  have hm : reserveMinCap 16 = 4 := rfl
  unfold reserveCapStride
  rw [hm]
  omega

/-- Affine `PhaseCreditSpec` for `Reserve16Env x`. -/
theorem phaseCredit_reserve16 {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (x : Reserve16Call) :
    let curLen := x.bs.length / 16
    let newCap := reserveCapStride 16 x.cap.toNat curLen 1
    PhaseCreditSpec M (Reserve16Env x)
      (32 * newCap + 9539) (16 * newCap + 8195)
      (16 * newCap + 8195) (16 * newCap) := by
  intro curLen newCap
  have hge4 : 4 ≤ newCap := reserveCapStride_16_ge_four x.cap.toNat curLen 1
  unfold Reserve16Env reserve16Events
  change PhaseCreditSpec M
    (· = if x.cap = 0#64 then rustAllocEvents (16 * newCap) 8
         else rustReallocEvents (16 * x.cap.toNat) (16 * newCap) 8)
    (32 * newCap + 9539) (16 * newCap + 8195) (16 * newCap + 8195) (16 * newCap)
  split
  · exact (PhaseCreditSpec.rustAlloc_aff hM (req := 16 * newCap) (al := 8) (by omega)).mono
      (by omega) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
  · exact (phaseCredit_rustRealloc_aff hM (old := 16 * x.cap.toNat) (new := 16 * newCap)
      (al := 8) (by omega) (by omega)).mono
      (by omega) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

/-- Affine `PhaseCreditSpec` for `TryAllocateInEnv x`. -/
theorem phaseCredit_tryAllocateIn {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (x : TryAllocateInCall) (hal : x.align.toNat ≤ 16) :
    let req := x.new.toNat * x.stride.toNat
    PhaseCreditSpec M (TryAllocateInEnv x)
      (2 * req + 9539) (req + 8195) (req + 8195) req := by
  intro req
  exact PhaseCreditSpec.rustAlloc_aff hM hal

/-! ## Phase M3 (`ReadStdinEnv` and `"coins"` `ReadFileEnv`) -/

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

theorem specCliIoReadSchedule_events_eq (K r : Nat) :
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

/-- Unconditional `PhaseCreditSpec` for `cliIoCapEvents (cliIoReadCaps 8 r)` (`read_stdin`, `≤ 1 MiB`). -/
theorem phaseCreditSpec_cliIoReadStdin_uncond {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (r : Nat) :
    PhaseCreditSpec M (· = cliIoCapEvents (cliIoReadCaps 8 r))
      4271963 1056771 1589254 1048576 where
  req_align := by
    rintro _ rfl
    exact req_align_cliIoReadCaps 8 r
  credit_le := by
    rintro st0 _ rfl
    exact stepEvents_cliIoReadStdin_uncond M hM.hSmallAff hM.hLargeAff hM.hMeta r st0

/-- `PhaseCreditSpec` for 3-arm `ReadStdinEnv stdin`. -/
theorem phaseCredit_readStdin {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (stdin : List (BitVec 8)) {stdinCap : Nat}
    (hstdin : stdin.length ≤ stdinCap) :
    PhaseCreditSpec M (ReadStdinEnv stdin)
      (max (2 * stdinCap + 9539) 4271963)
      (max (stdinCap + 8195) 1056771)
      (max (stdinCap + 8195) 1589254)
      (max stdinCap 1048576) := by
  unfold ReadStdinEnv
  have h1 : PhaseCreditSpec M (fun evs => evs = allocBytes1Events stdin)
      (max (2 * stdinCap + 9539) 4271963) (max (stdinCap + 8195) 1056771)
      (max (stdinCap + 8195) 1589254) (max stdinCap 1048576) :=
    (phaseCredit_allocBytes1_aff hM stdin hstdin).mono
      (Nat.le_max_left _ _) (Nat.le_max_left _ _)
      (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have h2 : PhaseCreditSpec M
      (fun evs => stdin.length ≤ 1048576 ∧
        evs = cliIoCapsEvents 0 (cliIoReadScheduleCaps 8 stdin.length))
      (max (2 * stdinCap + 9539) 4271963) (max (stdinCap + 8195) 1056771)
      (max (stdinCap + 8195) 1589254) (max stdinCap 1048576) :=
    (phaseCreditSpec_cliIoReadStdin_uncond hM stdin.length).congr_mono
      (fun evs h => by
        rw [← specCliIoReadSchedule_events_eq 8 stdin.length]
        exact h.2)
      (Nat.le_max_right _ _) (Nat.le_max_right _ _)
      (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have h3 : PhaseCreditSpec M
      (fun evs => 1048576 < stdin.length ∧
        evs = cliIoCapsEvents 0 (cliIoReadScheduleCaps 8 1048576) ++
          rustDeallocEvents 1048576 1)
      (max (2 * stdinCap + 9539) 4271963) (max (stdinCap + 8195) 1056771)
      (max (stdinCap + 8195) 1589254) (max stdinCap 1048576) := by
    have hseq := (phaseCreditSpec_cliIoReadStdin_uncond hM 1048576).seq
      (PhaseCreditSpec.freeOnly_of_hyps hM)
    refine hseq.congr_mono ?_ ?_ ?_ ?_ ?_
    · intro evs h
      refine Or.inr ⟨_, _, h.2, ?_, ?_⟩
      · exact specCliIoReadSchedule_events_eq 8 1048576
      · unfold FreeOnlyEvs rustDeallocEvents
        intro ev hev
        rw [List.mem_singleton] at hev
        exact ⟨1, 1048576, hev⟩
    · omega
    · omega
    · omega
    · omega
  exact (h1.or (h2.or h3)).mono (by omega) (by omega) (by omega) (by omega)

private theorem readFileResult_ok_length_le
    {files : String → Option FsEntry} {path bs : List (BitVec 8)} {fileCap : Nat}
    (hfb : ∀ p b, files p = some (.file b) → b.length ≤ fileCap)
    (hr : readFileResult files path = .ok bs) :
    bs.length ≤ fileCap := by
  unfold readFileResult readViewF at hr
  cases hba : blockingAncestorF files (pathStr path) <;> rw [hba] at hr
  · cases hf : files (pathStr path) <;> rw [hf] at hr
    · injection hr with hnil
      rw [← hnil]
      exact Nat.zero_le fileCap
    · rename_i entry
      cases entry with
      | file b =>
        dsimp only at hr
        split_ifs at hr
        injection hr with hb
        rw [← hb]
        exact hfb _ b hf
      | dir =>
        simp only at hr
        cases hr
  · rename_i a
    cases a <;> simp only at hr
    · injection hr with hnil
      rw [← hnil]
      exact Nat.zero_le fileCap
    · cases hr

/-- `PhaseCreditSpec` for 4-arm `ReadFileEnv files path` when every regular file has `≤ fileCap` bytes. -/
theorem phaseCredit_readFile_of_files_le {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (files : String → Option FsEntry) (path : List (BitVec 8))
    {fileCap : Nat} (hfb : ∀ p bs, files p = some (.file bs) → bs.length ≤ fileCap) :
    PhaseCreditSpec M (ReadFileEnv files path)
      (max (2 * fileCap + 9539) 8475806)
      (max (fileCap + 8195) 2105347)
      (max (fileCap + 8195) 3162118)
      (max fileCap 2097152) := by
  unfold ReadFileEnv
  cases hr : readFileResult files path with
  | error u =>
    cases u
    exact (PhaseCreditSpec.nil M).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  | ok bs =>
    dsimp only
    have hbs : bs.length ≤ fileCap := readFileResult_ok_length_le hfb hr
    have h1 : PhaseCreditSpec M (fun evs => evs = allocBytes1Events bs)
        (max (2 * fileCap + 9539) 8475806) (max (fileCap + 8195) 2105347)
        (max (fileCap + 8195) 3162118) (max fileCap 2097152) :=
      (phaseCredit_allocBytes1_aff hM bs hbs).mono
        (Nat.le_max_left _ _) (Nat.le_max_left _ _)
        (Nat.le_max_left _ _) (Nat.le_max_left _ _)
    have h2 : PhaseCreditSpec M
        (fun evs => (4096 ≤ path.length ∨ 0#8 ∈ path) ∧ evs = [])
        (max (2 * fileCap + 9539) 8475806) (max (fileCap + 8195) 2105347)
        (max (fileCap + 8195) 3162118) (max fileCap 2097152) :=
      (PhaseCreditSpec.of_eq_nil (M := M) (fun _ h => h.2)).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    have h3 : PhaseCreditSpec M
        (fun evs => bs.length ≤ 2097152 ∧
          evs = cliIoCapsEvents 0 (cliIoReadScheduleCaps 9 bs.length))
        (max (2 * fileCap + 9539) 8475806) (max (fileCap + 8195) 2105347)
        (max (fileCap + 8195) 3162118) (max fileCap 2097152) :=
      (phaseCreditSpec_cliIoReadFile_uncond hM bs.length).congr_mono
        (fun evs h => by
          rw [← specCliIoReadSchedule_events_eq 9 bs.length]
          exact h.2)
        (Nat.le_max_right _ _) (Nat.le_max_right _ _)
        (Nat.le_max_right _ _) (Nat.le_max_right _ _)
    have h4 : PhaseCreditSpec M
        (fun evs => 2097152 < bs.length ∧
          evs = cliIoCapsEvents 0 (cliIoReadScheduleCaps 9 2097152) ++
            rustDeallocEvents 2097152 1)
        (max (2 * fileCap + 9539) 8475806) (max (fileCap + 8195) 2105347)
        (max (fileCap + 8195) 3162118) (max fileCap 2097152) := by
      have hseq := (phaseCreditSpec_cliIoReadFile_uncond hM 2097152).seq
        (PhaseCreditSpec.freeOnly_of_hyps hM)
      refine hseq.congr_mono ?_ ?_ ?_ ?_ ?_
      · intro evs h
        refine Or.inr ⟨_, _, h.2, ?_, ?_⟩
        · exact specCliIoReadSchedule_events_eq 9 2097152
        · unfold FreeOnlyEvs rustDeallocEvents
          intro ev hev
          rw [List.mem_singleton] at hev
          exact ⟨1, 2097152, hev⟩
      · omega
      · omega
      · omega
      · omega
    exact (h1.or (h2.or (h3.or h4))).mono
      (by omega) (by omega) (by omega) (by omega)

/-! ## Phase M5 (`M5LoopAEntryEnv` Live Buffer Cancellation) and M6 (`LineWriter`) -/

/-- Scoped single-buffer tracker: `Env` leaves `0` net `liveLarge` when `cap ≤ smallMaxReq M` and
`largeCost M cap` net `liveLarge` when `smallMaxReq M < cap`, so trailing `rustDeallocEvents cap 1`
cancels `Δlive` to `0` across both regimes without case-splitting the caller. -/
private def CapLiveSpec (M : AllocCostModel) [HasFineReallocCredit M]
    (Env : List AllocEvent → Prop) (cap Δcum Δpeak maxReq : Nat) : Prop :=
  PhaseCreditSpec M Env Δcum
    (if HasFineReallocCredit.smallMaxReq M < cap then HasFineReallocCredit.largeCost M cap else 0)
    Δpeak maxReq

private theorem CapLiveSpec.alloc1 {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (cap : Nat) :
    CapLiveSpec M (· = rustAllocEvents cap 1) cap
      (2 * cap + 9539) (cap + 8195) cap := by
  unfold CapLiveSpec
  split
  · rename_i hgt
    have hm := hM.meta_le
    have hla := hM.largeCost_le hgt
    exact (PhaseCreditSpec.rustAlloc_large M (req := cap) (al := 1) (by omega) hgt).mono
      (by omega) (Nat.le_refl _) (by omega) (Nat.le_refl _)
  · rename_i hngt
    have hle : cap ≤ HasFineReallocCredit.smallMaxReq M := by omega
    have hsa := hM.smallAlloc_le hle
    exact (PhaseCreditSpec.rustAlloc_small_any hM (req := cap) (al := 1) (by omega) hle).mono
      (by omega) (Nat.le_refl _) (by omega) (Nat.le_refl _)

private theorem CapLiveSpec.realloc1 {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {E : List AllocEvent → Prop} {c₀ c₁ Δc Δp r : Nat}
    (hE : CapLiveSpec M E c₀ Δc Δp r)
    (hc₀_pos : 0 < c₀) (hle : c₀ ≤ c₁) :
    CapLiveSpec M (ConcatEnv E (· = rustReallocEvents c₀ c₁ 1)) c₁
      (Δc + (2 * c₁ + 9539))
      (max Δp (c₀ + c₁ + 2 * 8195))
      (max r c₁) := by
  unfold CapLiveSpec at hE ⊢
  have hc₁_pos : 0 < c₁ := by omega
  by_cases hg₀ : HasFineReallocCredit.smallMaxReq M < c₀
  · have hg₁ : HasFineReallocCredit.smallMaxReq M < c₁ := by omega
    simp only [hg₀, ↓reduceIte] at hE
    simp only [hg₁, ↓reduceIte]
    have hE' : PhaseCreditSpec M E Δc (0 + HasFineReallocCredit.largeCost M c₀) Δp r := by
      simpa using hE
    have hstep := PhaseCreditSpec.concat_rustRealloc_large_large hE'
      (al := 1) (new := c₁) (by omega) (by omega) hg₀ hg₁
    have hm := hM.meta_le
    have hla₀ := hM.largeCost_le hg₀
    have hla₁ := hM.largeCost_le hg₁
    exact hstep.mono (by omega) (by omega) (by omega) (Nat.le_refl _)
  · have hle₀ : c₀ ≤ HasFineReallocCredit.smallMaxReq M := by omega
    simp only [hg₀, ↓reduceIte] at hE
    by_cases hg₁ : HasFineReallocCredit.smallMaxReq M < c₁
    · simp only [hg₁, ↓reduceIte]
      have hre := PhaseCreditSpec.rustRealloc_small_large M (old := c₀) (new := c₁) (al := 1)
        (by omega) (by omega) hc₀_pos hle₀ hg₁
      have hm := hM.meta_le
      have hla₁ := hM.largeCost_le hg₁
      exact (hE.concat hre).mono (by omega) (by omega) (by omega) (Nat.le_refl _)
    · simp only [hg₁, ↓reduceIte]
      have hle₁ : c₁ ≤ HasFineReallocCredit.smallMaxReq M := by omega
      have hre := PhaseCreditSpec.rustRealloc_small_small M (old := c₀) (new := c₁) (al := 1)
        (by omega) (by omega) hc₀_pos hle₀ hc₁_pos hle₁
      have hsr := hM.smallRealloc_le hle₁
      exact (hE.concat hre).mono (by omega) (by omega) (by omega) (Nat.le_refl _)

private theorem CapLiveSpec.concat_zero_live {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {E₁ E₂ : List AllocEvent → Prop} {cap c₁ p₁ r₁ c₂ p₂ r₂ : Nat}
    (h₁ : CapLiveSpec M E₁ cap c₁ p₁ r₁)
    (h₂ : PhaseCreditSpec M E₂ c₂ 0 p₂ r₂) :
    CapLiveSpec M (ConcatEnv E₁ E₂) cap
      (c₁ + c₂) (max p₁ (cap + 8195 + p₂)) (max r₁ r₂) := by
  unfold CapLiveSpec at h₁ ⊢
  by_cases hg : HasFineReallocCredit.smallMaxReq M < cap
  · simp only [hg, ↓reduceIte] at h₁ ⊢
    have hla := hM.largeCost_le hg
    exact (h₁.concat h₂).mono (Nat.le_refl _) (by omega) (by omega) (Nat.le_refl _)
  · simp only [hg, ↓reduceIte] at h₁ ⊢
    exact (h₁.concat h₂).mono (Nat.le_refl _) (by omega) (by omega) (Nat.le_refl _)

private theorem CapLiveSpec.dealloc1_cancel {M : AllocCostModel} [HasFineReallocCredit M]
    {E : List AllocEvent → Prop} {cap Δc Δp r : Nat}
    (hE : CapLiveSpec M E cap Δc Δp r) :
    PhaseCreditSpec M (ConcatEnv E (· = rustDeallocEvents cap 1)) Δc 0 Δp r := by
  unfold CapLiveSpec at hE
  by_cases hg : HasFineReallocCredit.smallMaxReq M < cap
  · simp only [hg, ↓reduceIte] at hE
    have hE' : PhaseCreditSpec M E Δc (0 + HasFineReallocCredit.largeCost M cap) Δp r := by
      simpa using hE
    exact hE'.concat_dealloc_cancel (DeallocCreditSpec.free_large M (by omega) hg)
  · simp only [hg, ↓reduceIte] at hE
    have hle : cap ≤ HasFineReallocCredit.smallMaxReq M := by omega
    have hE' : PhaseCreditSpec M E Δc (0 + 0) Δp r := by simpa using hE
    exact hE'.concat_dealloc_cancel (DeallocCreditSpec.free_small M (by omega) hle)

/-- `PhaseCreditSpec` for `CliWriteFileEnv len` (`evs = []` or temporary `len + 1` buffer). -/
theorem phaseCredit_cliWriteFile {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (len : Nat) :
    PhaseCreditSpec M
      (fun evs => evs = [] ∨
        (384 ≤ len ∧ evs = rustAllocEvents (len + 1) 1 ++ rustDeallocEvents (len + 1) 1))
      (2 * (len + 1) + 9539) 0 ((len + 1) + 8195) (len + 1) := by
  refine (PhaseCreditSpec.or_of_imp (E₁ := (· = []))
    (E₂ := ConcatEnv (· = rustAllocEvents (len + 1) 1) (· = rustDeallocEvents (len + 1) 1))
    ?_ (PhaseCreditSpec.nil M)
    (PhaseCreditSpec.tempAllocFree_aff hM (req := len + 1) (al := 1) (by omega))).mono
    (by omega) (by omega) (by omega) (by omega)
  intro evs h
  rcases h with rfl | ⟨_, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨_, _, rfl, rfl, rfl⟩

/-- `PhaseCreditSpec` for `CliWriteStdoutEnv` (`1024`-B `LineWriter` allocation). -/
theorem phaseCredit_cliWriteStdout {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) :
    PhaseCreditSpec M (fun evs => evs = [] ∨ evs = rustAllocEvents 1024 1)
      (2 * 1024 + 9539) (1024 + 8195) (1024 + 8195) 1024 := by
  exact ((PhaseCreditSpec.nil M).or
    (PhaseCreditSpec.rustAlloc_aff hM (req := 1024) (al := 1) (by omega))).mono
    (by omega) (by omega) (by omega) (by omega)

private theorem reserveCap_bounds (cap len add : Nat) :
    len + add ≤ reserveCap cap len add ∧
    2 * cap ≤ reserveCap cap len add ∧
    8 ≤ reserveCap cap len add ∧
    reserveCap cap len add ≤ max (2 * cap) (max (len + add) 8) := by
  rw [← reserveCapStride_one]
  unfold reserveCapStride reserveMinCap
  simp only [↓reduceIte]
  omega

private theorem phaseCredit_m5LoopAEntry_core {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {cap0 cap1 capFinal writeLen maxCap : Nat} (need2 : Bool)
    (hc0_pos : 0 < cap0) (hc01 : cap0 ≤ cap1)
    (hc1F : cap1 ≤ capFinal) (hcF : capFinal ≤ maxCap)
    (hwlen : writeLen + 1 ≤ maxCap)
    (hcf_false : need2 = false → capFinal = cap1) :
    PhaseCreditSpec M
      (ConcatEnv
        (ConcatEnv
          (ConcatEnv
            (ConcatEnv (· = rustAllocEvents cap0 1) (· = rustReallocEvents cap0 cap1 1))
            (if need2 then (· = rustReallocEvents cap1 capFinal 1) else (· = [])))
          (fun evs => evs = [] ∨
            (384 ≤ writeLen ∧
              evs = rustAllocEvents (writeLen + 1) 1 ++ rustDeallocEvents (writeLen + 1) 1)))
        (· = rustDeallocEvents capFinal 1))
      (10 * maxCap + 4 * 9539) 0 (3 * maxCap + 3 * 8195) maxCap := by
  have hc1_pos : 0 < cap1 := Nat.lt_of_lt_of_le hc0_pos hc01
  have hs0 := CapLiveSpec.alloc1 hM cap0
  have hs1 := CapLiveSpec.realloc1 hM hs0 hc0_pos hc01
  have hs2 : CapLiveSpec M
      (ConcatEnv (ConcatEnv (· = rustAllocEvents cap0 1) (· = rustReallocEvents cap0 cap1 1))
        (if need2 then (· = rustReallocEvents cap1 capFinal 1) else (· = [])))
      capFinal
      ((2 * cap0 + 9539) + (2 * cap1 + 9539) + (2 * capFinal + 9539))
      (2 * maxCap + 2 * 8195) maxCap := by
    cases need2 with
    | true =>
      simp only [↓reduceIte]
      have hstep := CapLiveSpec.realloc1 hM hs1 hc1_pos hc1F
      unfold CapLiveSpec at hstep ⊢
      exact hstep.mono (by omega) (Nat.le_refl _) (by omega) (by omega)
    | false =>
      have hcf := hcf_false rfl
      subst hcf
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hstep := CapLiveSpec.concat_zero_live hM hs1 (PhaseCreditSpec.nil M)
      unfold CapLiveSpec at hstep ⊢
      exact hstep.mono (by omega) (Nat.le_refl _) (by omega) (by omega)
  have hwf := (phaseCredit_cliWriteFile hM writeLen).mono
    (c₂ := 2 * maxCap + 9539) (l₂ := 0) (p₂ := maxCap + 8195) (r₂ := maxCap)
    (by omega) (Nat.le_refl _) (by omega) hwlen
  have hs3 := CapLiveSpec.concat_zero_live hM hs2 hwf
  have hs4 := CapLiveSpec.dealloc1_cancel hs3
  exact hs4.mono (by omega) (Nat.le_refl _) (by omega) (by omega)

/-- Exact-order `PhaseCreditSpec` (`Δlive = 0`) for one non-empty-dir M5 commit entry
`alloc cap0 → realloc cap0 cap1 → optional realloc cap1 capFinal → CliWriteFileEnv → dealloc capFinal`. -/
theorem phaseCredit_m5LoopAEntry {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {dir name : List (BitVec 8)} {writeLen maxDir maxName : Nat}
    (hdir_ne : dir ≠ []) (hdir_le : dir.length ≤ maxDir) (hname_le : name.length ≤ maxName)
    (hwlen : writeLen + 1 ≤ max (4 * maxDir + maxName + 16) 16) :
    let cap0 := dir.length
    let cap1 := reserveCap cap0 cap0 1
    let need2 := decide (cap1 - (cap0 + 1) < name.length)
    let capFinal := if need2 then reserveCap cap1 (cap0 + 1) name.length else cap1
    let maxCap := max (4 * maxDir + maxName + 16) 16
    PhaseCreditSpec M
      (ConcatEnv
        (ConcatEnv
          (ConcatEnv
            (ConcatEnv (· = rustAllocEvents cap0 1) (· = rustReallocEvents cap0 cap1 1))
            (if need2 then (· = rustReallocEvents cap1 capFinal 1) else (· = [])))
          (fun evs => evs = [] ∨
            (384 ≤ writeLen ∧
              evs = rustAllocEvents (writeLen + 1) 1 ++ rustDeallocEvents (writeLen + 1) 1)))
        (· = rustDeallocEvents capFinal 1))
      (10 * maxCap + 4 * 9539) 0 (3 * maxCap + 3 * 8195) maxCap := by
  intro cap0 cap1 need2 capFinal maxCap
  have hc0_pos : 0 < cap0 := List.length_pos_iff.mpr hdir_ne
  obtain ⟨_, hb1_2c, _, hb1_hi⟩ := reserveCap_bounds cap0 cap0 1
  have hc01 : cap0 ≤ cap1 := by omega
  have hcap1_le : cap1 ≤ 2 * maxDir + 8 := by omega
  obtain ⟨_, hb2_2c, _, hb2_hi⟩ := reserveCap_bounds cap1 (cap0 + 1) name.length
  have hrc2_ge : cap1 ≤ reserveCap cap1 (cap0 + 1) name.length := by omega
  have hrc2_le : reserveCap cap1 (cap0 + 1) name.length ≤ 4 * maxDir + maxName + 16 := by omega
  have hc1F : cap1 ≤ capFinal := by
    dsimp [capFinal]
    cases need2
    · exact Nat.le_refl _
    · exact hrc2_ge
  have hcF : capFinal ≤ maxCap := by
    refine Nat.le_trans ?_ (Nat.le_max_left _ _)
    dsimp [capFinal]
    cases need2
    · simp only [Bool.false_eq_true, ↓reduceIte]
      omega
    · simp only [↓reduceIte]
      exact hrc2_le
  exact phaseCredit_m5LoopAEntry_core hM need2 hc0_pos hc01 hc1F hcF hwlen
    (fun hnf => by simp [capFinal, hnf])

/-! ## Phases M1, M2 (`argv` and `M2CollectEnv`), and Zero-Live Loops -/

/-- Affine `PhaseCreditSpec` for `M1PhaseEnv argvLen` when `argvLen ≤ 3`. -/
theorem phaseCredit_m1Phase {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {argvLen : Nat} (hargv : argvLen ≤ 3) :
    PhaseCreditSpec M (fun evs => evs = [] ∨ evs = rustAllocEvents (16 * argvLen) 8)
      (2 * 48 + 9539) (48 + 8195) (48 + 8195) 48 := by
  exact ((PhaseCreditSpec.nil M).or
    (PhaseCreditSpec.rustAlloc_aff hM (req := 16 * argvLen) (al := 8) (by omega))).mono
    (by omega) (by omega) (by omega) (by omega)

/-- Small-regime `PhaseCreditSpec` for `M1PhaseEnv argvLen` (`Δlive = 0`, `Δpeak = 0`) when
`64 ≤ smallMaxReq M` and `argvLen ≤ 3`. -/
theorem phaseCredit_m1Phase_small64 {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsm64 : 64 ≤ HasFineReallocCredit.smallMaxReq M)
    {argvLen : Nat} (hargv : argvLen ≤ 3) :
    PhaseCreditSpec M (fun evs => evs = [] ∨ evs = rustAllocEvents (16 * argvLen) 8)
      (2 * 48 + 9539) 0 0 48 := by
  have hle : 16 * argvLen ≤ HasFineReallocCredit.smallMaxReq M := by omega
  have hsa := hM.smallAlloc_le hle
  exact ((PhaseCreditSpec.nil M).or
    (PhaseCreditSpec.rustAlloc_small_any hM (req := 16 * argvLen) (al := 8)
      (by omega) hle)).mono
    (by omega) (by omega) (by omega) (by omega)

private theorem reserveCapStride_16_eq_four_of_lt_three {k : Nat} (hk : k < 3) :
    reserveCapStride 16 k k 1 = 4 := by
  have hm : reserveMinCap 16 = 4 := rfl
  unfold reserveCapStride
  rw [hm]
  omega

/-- Affine `PhaseCreditSpec` for `M2CollectEnv argvLen` when `argvLen ≤ 3`. -/
theorem phaseCredit_m2Collect {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {argvLen : Nat} (hargv : argvLen ≤ 3) :
    PhaseCreditSpec M
      (IterSeqEnv
        (fun k evs =>
          evs = [] ∨ evs = rustReallocEvents (16 * k) (16 * reserveCapStride 16 k k 1) 8)
        (List.range argvLen))
      (3 * (2 * 64 + 9539)) (3 * (64 + 8195)) (4 * (64 + 8195)) 64 := by
  have hit := PhaseCreditSpec.iter_const (M := M)
    (Step := fun k evs =>
      evs = [] ∨ evs = rustReallocEvents (16 * k) (16 * reserveCapStride 16 k k 1) 8)
    (c := 2 * 64 + 9539) (l := 64 + 8195) (p := 64 + 8195) (r := 64)
    (List.range argvLen) ?_
  · rw [List.length_range] at hit
    exact hit.mono (by omega) (by omega) (by omega) (Nat.le_refl 64)
  · intro k hk
    have hk3 : k < 3 := Nat.lt_of_lt_of_le (List.mem_range.mp hk) hargv
    have hcap : reserveCapStride 16 k k 1 = 4 := reserveCapStride_16_eq_four_of_lt_three hk3
    rw [hcap]
    exact ((PhaseCreditSpec.nil M).or
      (phaseCredit_rustRealloc_aff hM (old := 16 * k) (new := 16 * 4) (al := 8)
        (by omega) (by omega))).mono
      (by omega) (by omega) (by omega) (by omega)

/-- Small-regime `PhaseCreditSpec` for `M2CollectEnv argvLen` (`Δlive = 0`, `Δpeak = 0`) when
`64 ≤ smallMaxReq M` and `argvLen ≤ 3`. -/
theorem phaseCredit_m2Collect_small64 {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsm64 : 64 ≤ HasFineReallocCredit.smallMaxReq M)
    {argvLen : Nat} (hargv : argvLen ≤ 3) :
    PhaseCreditSpec M
      (IterSeqEnv
        (fun k evs =>
          evs = [] ∨ evs = rustReallocEvents (16 * k) (16 * reserveCapStride 16 k k 1) 8)
        (List.range argvLen))
      (3 * (2 * 64 + 9539)) 0 0 64 := by
  have hit := PhaseCreditSpec.iter_zero_live (M := M)
    (Step := fun k evs =>
      evs = [] ∨ evs = rustReallocEvents (16 * k) (16 * reserveCapStride 16 k k 1) 8)
    (c := 2 * 64 + 9539) (p := 0) (r := 64)
    (List.range argvLen) ?_
  · rw [List.length_range] at hit
    exact hit.mono (by omega) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 64)
  · intro k hk
    have hk3 : k < 3 := Nat.lt_of_lt_of_le (List.mem_range.mp hk) hargv
    have hcap : reserveCapStride 16 k k 1 = 4 := reserveCapStride_16_eq_four_of_lt_three hk3
    rw [hcap]
    exact ((PhaseCreditSpec.nil M).or
      (phaseCredit_rustRealloc_small_any hM (old := 16 * k) (new := 16 * 4) (al := 8)
        (by omega) (by omega) (by omega) (by omega))).mono
      (by omega) (by omega) (by omega) (by omega)

/-- Zero-net-live loop combinator with per-element `Δcum := c x` and uniform `(Δpeak, maxReq) := (p, r)`:
sums `(xs.map c).sum` while keeping `Δlive = 0` and `Δpeak = p`. -/
theorem phaseCredit_iter_sum_zero_live {α : Type} {M : AllocCostModel} [HasFineReallocCredit M]
    {Step : α → List AllocEvent → Prop} (c : α → Nat) {p r : Nat} (xs : List α)
    (hstep : ∀ x ∈ xs, PhaseCreditSpec M (Step x) (c x) 0 p r) :
    PhaseCreditSpec M (IterSeqEnv Step xs) ((xs.map c).sum) 0 p r := by
  induction xs with
  | nil =>
    exact (PhaseCreditSpec.nil M).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  | cons x xs ih =>
    have hx := hstep x List.mem_cons_self
    have hxs := ih (fun y hy => hstep y (List.mem_cons_of_mem x hy))
    exact (hx.seq hxs).mono
      (by simp only [List.map_cons, List.sum_cons]; omega)
      (by omega) (by omega) (by omega)

theorem map_mul_sum_eq {α : Type} (f : α → Nat) (K : Nat) (xs : List α) :
    (xs.map (fun x => f x * K)).sum = (xs.map f).sum * K := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih, Nat.add_mul]

/-! ## `read_stdin` Doubling Schedule and Tight `M3` Bounds -/

/-- `CliIo` doubling-schedule envelope (`K = 8`, `≤ 1 MiB`) for `signal_session_io::read_stdin`. -/
def CliIoReadStdinEnv (r : Nat) (evs : List AllocEvent) : Prop :=
  evs = cliIoCapEvents (cliIoReadCaps 8 r)

/-- `CliIo` doubling-schedule envelope (`K = 9`, `≤ 2 MiB`) for `signal_session_io::read_file`. -/
def CliIoReadFileEnv (r : Nat) (evs : List AllocEvent) : Prop :=
  evs = cliIoCapEvents (cliIoReadCaps 9 r)

/-- Tight `read_stdin` (`j = 8`) `cumSmall` bound: `cliIoTightCumBound 8 = 573,696` B. -/
def readStdinCliIoDeltaCumTight : Nat := 573696

def readStdinCliIoDeltaLive : Nat := 1056771

/-- `read_stdin` (`j = 8`) `peakLarge` overlap bound: `cliIoStepPeakBound 8 = 1,589,254` B. -/
def readStdinCliIoDeltaPeak : Nat := 1589254

def readStdinCliIoMaxReq : Nat := 1048576

/-- Tight `read_file` (`j = 9`) `cumSmall` bound: `cliIoTightCumBound 9 = 573,818` B. -/
def readFileCliIoDeltaCumTight : Nat := 573818

def readFileCliIoDeltaLive : Nat := 2105347

/-- `read_file` (`j = 9`) `peakLarge` overlap bound: `cliIoStepPeakBound 9 = 3,162,118` B. -/
def readFileCliIoDeltaPeak : Nat := 3162118

def readFileCliIoMaxReq : Nat := 2097152

/-- Tight `read_stdin` (`cliIoReadCaps 8 r`, `≤ 1 MiB`) credit bound when
`131072 ≤ smallMaxReq M < 262144`. -/
theorem stepEvents_cliIoReadStdin_tight (M : AllocCostModel) [HasFineReallocCredit M]
    (hSmLo : 131072 ≤ HasFineReallocCredit.smallMaxReq M)
    (hSmHi : HasFineReallocCredit.smallMaxReq M < 262144)
    (hSmallAff : ∀ r ≤ HasFineReallocCredit.smallMaxReq M,
      HasFineReallocCredit.smallAllocCost M r ≤ 2 * r + 9539 ∧
      HasFineReallocCredit.smallReallocCost M r ≤ 2 * r + 9539)
    (hLargeAff : ∀ r, HasFineReallocCredit.smallMaxReq M < r →
      HasFineReallocCredit.largeCost M r ≤ r + 8195)
    (hMeta : HasFineReallocCredit.largeMetaCost M ≤ 122)
    (r : Nat) (st0 : M.σ) :
    let st' := M.stepEvents (cliIoCapEvents (cliIoReadCaps 8 r)) st0
    HasFineReallocCredit.cumSmall st' ≤ HasFineReallocCredit.cumSmall st0 + 573696 ∧
    HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st0 + 1056771 ∧
    HasFineReallocCredit.peakLarge st' ≤
      max (HasFineReallocCredit.peakLarge st0) (HasFineReallocCredit.liveLarge st0 + 1589254) := by
  dsimp only
  by_cases hr : r = 0
  · subst hr
    rw [cliIoCapEvents_readCaps_zero, M.stepEvents_nil]
    omega
  · have hr_pos : 0 < r := by omega
    rw [cliIoCapEvents_readCaps_pos hr_pos]
    set j := cliIoCapIdx 8 r
    have hj : j ≤ 8 := cliIoCapIdx_le 8 r
    have hseq := stepEvents_cliIoCapSeq_tight M hSmLo hSmHi hSmallAff hLargeAff hMeta st0 j
    dsimp only at hseq
    have hcum_m : cliIoTightCumBound j ≤ 573696 := by
      rw [← cliIoTightCumBound_eight]
      exact cliIoTightCumBound_mono hj
    have hcap_le : cliIoCap j ≤ 1048576 := by
      have h8 : cliIoCap 8 = 1048576 := rfl
      rw [← h8]
      exact cliIoCap_mono hj
    have hlive_m : cliIoStepLiveBound M j ≤ 1056771 := by
      unfold cliIoStepLiveBound
      split
      · omega
      · rename_i hnot
        have hlc := hLargeAff (cliIoCap j) (by omega)
        omega
    have hpeak_m : cliIoStepPeakBound j ≤ 1589254 := by
      have hp8 : cliIoStepPeakBound 8 = 1589254 := rfl
      rw [← hp8]
      exact cliIoStepPeakBound_mono hj
    exact ⟨by omega, by omega, by omega⟩

/-- Tight `PhaseCreditSpec` (`Δcum = 573,696`) for `cliIoCapEvents (cliIoReadCaps 8 r)` when
`131072 ≤ smallMaxReq M < 262144`. -/
theorem phaseCreditSpec_cliIoReadStdin_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M)
    (hSmLo : 131072 ≤ HasFineReallocCredit.smallMaxReq M)
    (hSmHi : HasFineReallocCredit.smallMaxReq M < 262144)
    (r : Nat) :
    PhaseCreditSpec M (· = cliIoCapEvents (cliIoReadCaps 8 r))
      573696 1056771 1589254 1048576 where
  req_align := by
    rintro _ rfl
    exact req_align_cliIoReadCaps 8 r
  credit_le := by
    rintro st0 _ rfl
    exact stepEvents_cliIoReadStdin_tight M hSmLo hSmHi hM.hSmallAff hM.hLargeAff hM.hMeta r st0

theorem phaseCreditSpec_cliIoReadStdin_anyR_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M)
    (hSmLo : 131072 ≤ HasFineReallocCredit.smallMaxReq M)
    (hSmHi : HasFineReallocCredit.smallMaxReq M < 262144) :
    PhaseCreditSpec M (fun evs => ∃ r, CliIoReadStdinEnv r evs)
      573696 1056771 1589254 1048576 where
  req_align := by
    rintro _ ⟨r, h⟩
    rw [h]
    exact req_align_cliIoReadCaps 8 r
  credit_le := by
    rintro st0 _ ⟨r, h⟩
    rw [h]
    exact stepEvents_cliIoReadStdin_tight M hSmLo hSmHi hM.hSmallAff hM.hLargeAff hM.hMeta r st0

theorem phaseCreditSpec_cliIoReadFile_anyR_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M)
    (hSmLo : 131072 ≤ HasFineReallocCredit.smallMaxReq M)
    (hSmHi : HasFineReallocCredit.smallMaxReq M < 262144) :
    PhaseCreditSpec M (fun evs => ∃ r, CliIoReadFileEnv r evs)
      573818 2105347 3162118 2097152 where
  req_align := by
    rintro _ ⟨r, h⟩
    exact (phaseCreditSpec_cliIoReadFile_tight hM hSmLo hSmHi r).req_align _ h
  credit_le := by
    rintro st0 _ ⟨r, h⟩
    exact (phaseCreditSpec_cliIoReadFile_tight hM hSmLo hSmHi r).credit_le st0 h

theorem readStdin_cliIo_phaseCredit_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M)
    (hSmLo : 131072 ≤ HasFineReallocCredit.smallMaxReq M)
    (hSmHi : HasFineReallocCredit.smallMaxReq M < 262144)
    (r : Nat) :
    PhaseCreditSpec M (CliIoReadStdinEnv r)
      readStdinCliIoDeltaCumTight readStdinCliIoDeltaLive
      readStdinCliIoDeltaPeak readStdinCliIoMaxReq :=
  phaseCreditSpec_cliIoReadStdin_tight hM hSmLo hSmHi r

theorem readFile_cliIo_phaseCredit_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M)
    (hSmLo : 131072 ≤ HasFineReallocCredit.smallMaxReq M)
    (hSmHi : HasFineReallocCredit.smallMaxReq M < 262144)
    (r : Nat) :
    PhaseCreditSpec M (CliIoReadFileEnv r)
      readFileCliIoDeltaCumTight readFileCliIoDeltaLive
      readFileCliIoDeltaPeak readFileCliIoMaxReq :=
  phaseCreditSpec_cliIoReadFile_tight hM hSmLo hSmHi r

/-- Tight `PhaseCreditSpec` for single-buffer `allocBytes1Events bs` (`bs.length ≤ cap`) when
`smallMaxReq M < 262144`:
- if `bs.length ≤ smallMaxReq M` (`≤ 262,143`), `Δcum ≤ 2 * 262143 + 9539 = 533,825 ≤ 573,696`
  and `Δlive = Δpeak = 0`;
- if `smallMaxReq M < bs.length`, `Δcum ≤ largeMetaCost M ≤ 122` and `Δlive = Δpeak ≤ cap + 8195`. -/
theorem phaseCredit_allocBytes1_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hSmHi : HasFineReallocCredit.smallMaxReq M < 262144)
    (bs : List (BitVec 8)) {cap : Nat} (hlen : bs.length ≤ cap) :
    PhaseCreditSpec M (· = allocBytes1Events bs)
      533825 (cap + 8195) (cap + 8195) cap := by
  unfold allocBytes1Events
  split
  · exact (PhaseCreditSpec.nil M).mono (by omega) (by omega) (by omega) (by omega)
  · by_cases hsm : bs.length ≤ HasFineReallocCredit.smallMaxReq M
    · have hsa := hM.smallAlloc_le hsm
      exact (PhaseCreditSpec.rustAlloc_small_any hM (req := bs.length) (al := 1)
        (by omega) hsm).mono (by omega) (by omega) (by omega) hlen
    · have hgt : HasFineReallocCredit.smallMaxReq M < bs.length := by omega
      have hm := hM.meta_le
      have hla := hM.largeCost_le hgt
      exact (PhaseCreditSpec.rustAlloc_large M (req := bs.length) (al := 1)
        (by omega) hgt).mono (by omega) (by omega) (by omega) hlen

/-- Tight `PhaseCreditSpec` (`Δcum = 573,696`) for `ReadStdinEnv stdin` when `131072 ≤ smallMaxReq M < 262144`. -/
theorem phaseCredit_readStdin_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M)
    (hSmLo : 131072 ≤ HasFineReallocCredit.smallMaxReq M)
    (hSmHi : HasFineReallocCredit.smallMaxReq M < 262144)
    (stdin : List (BitVec 8)) {stdinCap : Nat}
    (hstdin : stdin.length ≤ stdinCap) :
    PhaseCreditSpec M (ReadStdinEnv stdin)
      573696
      (max (stdinCap + 8195) 1056771)
      (max (stdinCap + 8195) 1589254)
      (max stdinCap 1048576) := by
  unfold ReadStdinEnv
  have h1 : PhaseCreditSpec M (fun evs => evs = allocBytes1Events stdin)
      573696 (max (stdinCap + 8195) 1056771)
      (max (stdinCap + 8195) 1589254) (max stdinCap 1048576) :=
    (phaseCredit_allocBytes1_tight hM hSmHi stdin hstdin).mono
      (by decide) (Nat.le_max_left _ _)
      (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have h2 : PhaseCreditSpec M
      (fun evs => stdin.length ≤ 1048576 ∧
        evs = cliIoCapsEvents 0 (cliIoReadScheduleCaps 8 stdin.length))
      573696 (max (stdinCap + 8195) 1056771)
      (max (stdinCap + 8195) 1589254) (max stdinCap 1048576) :=
    (phaseCreditSpec_cliIoReadStdin_tight hM hSmLo hSmHi stdin.length).congr_mono
      (fun evs h => by
        rw [← specCliIoReadSchedule_events_eq 8 stdin.length]
        exact h.2)
      (Nat.le_refl _) (Nat.le_max_right _ _)
      (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have h3 : PhaseCreditSpec M
      (fun evs => 1048576 < stdin.length ∧
        evs = cliIoCapsEvents 0 (cliIoReadScheduleCaps 8 1048576) ++
          rustDeallocEvents 1048576 1)
      573696 (max (stdinCap + 8195) 1056771)
      (max (stdinCap + 8195) 1589254) (max stdinCap 1048576) := by
    have hseq := (phaseCreditSpec_cliIoReadStdin_tight hM hSmLo hSmHi 1048576).seq
      (PhaseCreditSpec.freeOnly_of_hyps hM)
    refine hseq.congr_mono ?_ ?_ ?_ ?_ ?_
    · intro evs h
      refine Or.inr ⟨_, _, h.2, ?_, ?_⟩
      · exact specCliIoReadSchedule_events_eq 8 1048576
      · unfold FreeOnlyEvs rustDeallocEvents
        intro ev hev
        rw [List.mem_singleton] at hev
        exact ⟨1, 1048576, hev⟩
    · omega
    · omega
    · omega
    · omega
  exact (h1.or (h2.or h3)).mono (by omega) (by omega) (by omega) (by omega)

/-- Tight `PhaseCreditSpec` (`Δcum = 573,818`) for `ReadFileEnv files path` when
`131072 ≤ smallMaxReq M < 262144` and every regular file has `≤ fileCap` bytes. -/
theorem phaseCredit_readFile_of_files_le_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M)
    (hSmLo : 131072 ≤ HasFineReallocCredit.smallMaxReq M)
    (hSmHi : HasFineReallocCredit.smallMaxReq M < 262144)
    (files : String → Option FsEntry) (path : List (BitVec 8))
    {fileCap : Nat} (hfb : ∀ p bs, files p = some (.file bs) → bs.length ≤ fileCap) :
    PhaseCreditSpec M (ReadFileEnv files path)
      573818
      (max (fileCap + 8195) 2105347)
      (max (fileCap + 8195) 3162118)
      (max fileCap 2097152) := by
  unfold ReadFileEnv
  cases hr : readFileResult files path with
  | error u =>
    cases u
    exact (PhaseCreditSpec.nil M).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  | ok bs =>
    dsimp only
    have hbs : bs.length ≤ fileCap := readFileResult_ok_length_le hfb hr
    have h1 : PhaseCreditSpec M (fun evs => evs = allocBytes1Events bs)
        573818 (max (fileCap + 8195) 2105347)
        (max (fileCap + 8195) 3162118) (max fileCap 2097152) :=
      (phaseCredit_allocBytes1_tight hM hSmHi bs hbs).mono
        (by decide) (Nat.le_max_left _ _)
        (Nat.le_max_left _ _) (Nat.le_max_left _ _)
    have h2 : PhaseCreditSpec M
        (fun evs => (4096 ≤ path.length ∨ 0#8 ∈ path) ∧ evs = [])
        573818 (max (fileCap + 8195) 2105347)
        (max (fileCap + 8195) 3162118) (max fileCap 2097152) :=
      (PhaseCreditSpec.of_eq_nil (M := M) (fun _ h => h.2)).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    have h3 : PhaseCreditSpec M
        (fun evs => bs.length ≤ 2097152 ∧
          evs = cliIoCapsEvents 0 (cliIoReadScheduleCaps 9 bs.length))
        573818 (max (fileCap + 8195) 2105347)
        (max (fileCap + 8195) 3162118) (max fileCap 2097152) :=
      (phaseCreditSpec_cliIoReadFile_tight hM hSmLo hSmHi bs.length).congr_mono
        (fun evs h => by
          rw [← specCliIoReadSchedule_events_eq 9 bs.length]
          exact h.2)
        (Nat.le_refl _) (Nat.le_max_right _ _)
        (Nat.le_max_right _ _) (Nat.le_max_right _ _)
    have h4 : PhaseCreditSpec M
        (fun evs => 2097152 < bs.length ∧
          evs = cliIoCapsEvents 0 (cliIoReadScheduleCaps 9 2097152) ++
            rustDeallocEvents 2097152 1)
        573818 (max (fileCap + 8195) 2105347)
        (max (fileCap + 8195) 3162118) (max fileCap 2097152) := by
      have hseq := (phaseCreditSpec_cliIoReadFile_tight hM hSmLo hSmHi 2097152).seq
        (PhaseCreditSpec.freeOnly_of_hyps hM)
      refine hseq.congr_mono ?_ ?_ ?_ ?_ ?_
      · intro evs h
        refine Or.inr ⟨_, _, h.2, ?_, ?_⟩
        · exact specCliIoReadSchedule_events_eq 9 2097152
        · unfold FreeOnlyEvs rustDeallocEvents
          intro ev hev
          rw [List.mem_singleton] at hev
          exact ⟨1, 2097152, hev⟩
      · omega
      · omega
      · omega
      · omega
    exact (h1.or (h2.or (h3.or h4))).mono
      (by omega) (by omega) (by omega) (by omega)

/-- Small-regime `PhaseCreditSpec` for `CliWriteStdoutEnv` (`1024`-B `LineWriter`, `Δlive = 0`,
`Δpeak = 0`) when `1024 ≤ smallMaxReq M`. -/
theorem phaseCredit_cliWriteStdout_small1024 {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsm1024 : 1024 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (fun evs => evs = [] ∨ evs = rustAllocEvents 1024 1)
      (2 * 1024 + 9539) 0 0 1024 := by
  have hsa := hM.smallAlloc_le hsm1024
  exact ((PhaseCreditSpec.nil M).or
    (PhaseCreditSpec.rustAlloc_small_any hM (req := 1024) (al := 1)
      (by omega) hsm1024)).mono
    (by omega) (by omega) (by omega) (by omega)

end LibsignalBinary.Proofs.PeakBudget.CliMainIoCredit
