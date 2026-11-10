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
public import LibsignalBinary.Proofs.PeakBudget.CliRunPeakHelpers
public import LibsignalBinary.Proofs.PeakBudget.DirPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromHelpers
public import LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.WireSignalHelpers
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Concat2Budget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserialize.SpecBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget

/-!
# Exact-Order `signal_session::run` Helper and Arm Peak Envelopes

Sequential `AllocEvent` envelopes and symbolic `PhaseCreditSpec M` bounds for `signal_session::run`
(`R0 → Arm → Join`) across `.keygen`, `.init` (`R1a → R1b → R1c`), `.send` (`R2`), and `.recv`
(`R3a | R3b | RecvBad`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak

open VerifiedLibraries.Mallocng.Proofs (sizeToClassUnits)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalTripleRatchet (TryFromGhost)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser serviceIdParse uuidTryParse)
open CryptoVerification.SignalSession.Cli (DirGhost ReadRule StoresGhost pathOf utf8)
open CryptoVerification.SignalSession.Cli.MainHops (AddrV CallV RunCall addrParse parseUnsigned rsplitDot)
open CryptoVerification.SignalSession.Cli.RunCompose (runFiles)
open CryptoVerification.SignalSession.Cli.RunProofs (kemPkLen)
open LibsignalBinary.Heap (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv rustAllocEvents)
open LibsignalBinary.Heap.Fine
  (FineScale MmapThresholdReq coarseWt_le_cap fineCostModel fineLargeCost fineSmallAllocCost)
open LibsignalBinary.Heap.Fine.ClientBounds
  (fineCostModel_largeCost_eq fineCostModel_smallMaxReq_eq)
open LibsignalBinary.Heap.SpecBudget (allocBytes1Events)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
  (DirDomainCaps addrParse_name_length_le dirDomainCaps_opened_own)
open LibsignalBinary.Proofs.PeakBudget.CliRunPeakHelpers
  (deallocBytes1OfLen freeOnlyEvs_of_seqEnv phaseCredit_allocBytes1OfLen_aff
   phaseCredit_or_freeOnly_left phaseCredit_runDispatch
   phaseCredit_seq_freeOnly_left phaseCredit_seq_freeOnly_right
   phaseCredit_tempAllocBytes1BodyFree_le)
open LibsignalBinary.Proofs.PeakBudget.DirPeakSpec
  (CliDirGetEnv CliPathEnv dirGetRuleDeltaCum dirGetRuleDeltaLive dirGetRuleDeltaPeak
   dirGetRuleMaxReq dirGet_rule_phaseCredit pathDeltaCum pathDeltaLive pathDeltaPeak
   pathMaxReq path_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (ConcatEnv FreeOnlyAlign16Evs ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec
  (SigTryFromBoundedEnv SigTryFromCaps SigTryFromLoopBoundedEnv SigTryFromPostEnv
   WireLowInterceptHyps fineCostModel_wireLowInterceptHyps
   sigTryFromCapDeltaCum sigTryFromCapDeltaLive sigTryFromCapDeltaPeak sigTryFromCapMaxReq
   sigTryFromDeltaCum sigTryFromDeltaCum_le_cap sigTryFromDeltaLive sigTryFromDeltaLive_le_cap
   sigTryFromDeltaPeak sigTryFromDeltaPeak_le_cap sigTryFromMaxReq sigTryFromMaxReq_le_cap
   sigTryFrom_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromHelpers (tryCloneSmallDelta)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromPeakSpec
  (PksmTryFromBoundedEnv pksmDecodedInnerBytes_length_le pksmInnerGhost
   pksmTryFromCapDeltaCum pksmTryFromCapDeltaLive pksmTryFromCapDeltaPeak pksmTryFromCapMaxReq
   pksmTryFromDeltaCum pksmTryFromDeltaCum_le_cap pksmTryFromDeltaLive pksmTryFromDeltaLive_le_cap
   pksmTryFromDeltaPeak pksmTryFromDeltaPeak_le_cap pksmTryFromMaxReq pksmTryFromMaxReq_le_cap
   pksmTryFrom_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.WireSignalHelpers
  (bytesCumAlloc bytesCumAlloc_le_aff bytesLargeLive bytesLargeLive_zero
   req_align_of_rustAllocEvents stepEvents_rustAlloc_pos)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget (addressEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Concat2Budget (cliConcat2Events)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserialize.SpecBudget
  (kemDeserializeEvents)
open CryptoVerification.SignalSession.Cli.RunCompose (PksmGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)

/-! ## Algebraic, Existential, and UTF-8 Helpers -/

/-- Guarded existential `PhaseCreditSpec` combinator, bridging ghost-indexed `SemPlacedBudget`
slot envelopes (`InitGhost`, `EncGhost`, `DecSigGhost`, `DecPkGhost`) to `CliRunCalleeEnvs`. -/
theorem phaseCredit_exists_guarded {α : Type} {M : AllocCostModel} [HasFineReallocCredit M]
    {P : α → Prop} {E : α → List AllocEvent → Prop} {c l p r : Nat}
    (h : ∀ x, P x → PhaseCreditSpec M (E x) c l p r) :
    PhaseCreditSpec M (fun evs => ∃ x, P x ∧ E x evs) c l p r where
  req_align evs := fun ⟨x, hx, he⟩ => (h x hx).req_align evs he
  credit_le st0 := fun ⟨x, hx, he⟩ => (h x hx).credit_le st0 he

theorem freeOnlyEvs_append {evs₁ evs₂ : List AllocEvent}
    (h₁ : FreeOnlyEvs evs₁) (h₂ : FreeOnlyEvs evs₂) : FreeOnlyEvs (evs₁ ++ evs₂) :=
  freeOnlyEvs_of_seqEnv (fun _ h => h) (fun _ h => h) (Or.inr ⟨evs₁, evs₂, rfl, h₁, h₂⟩)

private theorem max_le_max {a₁ a₂ b₁ b₂ : Nat} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
    max a₁ b₁ ≤ max a₂ b₂ :=
  Nat.max_le.mpr ⟨Nat.le_trans ha (Nat.le_max_left _ _), Nat.le_trans hb (Nat.le_max_right _ _)⟩

private theorem max3_mono {a₁ b₁ c₁ a₂ b₂ c₂ : Nat} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) (hc : c₁ ≤ c₂) :
    max a₁ (max b₁ c₁) ≤ max a₂ (max b₂ c₂) :=
  max_le_max ha (max_le_max hb hc)

theorem freeOnlyEvs_deallocBytes1OfLen (n : Nat) : FreeOnlyEvs (deallocBytes1OfLen n) := by
  unfold deallocBytes1OfLen; split
  · exact FreeOnlyAlign16Evs.nil.toFreeOnlyEvs
  · exact (FreeOnlyAlign16Evs.rustDealloc (by decide) n).toFreeOnlyEvs

theorem freeOnlyEvs_seq_deallocBytes1OfLen (n : Nat) :
    ∀ evs, SeqEnv (fun e => e = deallocBytes1OfLen n) FreeOnlyEvs evs → FreeOnlyEvs evs :=
  fun _ => freeOnlyEvs_of_seqEnv
    (by rintro _ rfl; exact freeOnlyEvs_deallocBytes1OfLen n) (fun _ h => h)

theorem pathDeltaLive_le_peak (maxDir maxName : Nat) :
    pathDeltaLive maxDir maxName ≤ pathDeltaPeak maxDir maxName := by
  unfold pathDeltaLive pathDeltaPeak; generalize max (4 * maxDir + maxName + 16) 16 = m; omega

theorem dirGetRuleDeltaLive_le_peak (maxDir maxName maxVal fileCap : Nat) :
    dirGetRuleDeltaLive maxDir maxName maxVal fileCap ≤
      dirGetRuleDeltaPeak maxDir maxName maxVal fileCap := by
  have hp := pathDeltaLive_le_peak maxDir maxName
  have hrf : DirPeakSpec.readFileRuleDeltaLive fileCap ≤
      DirPeakSpec.readFileRuleDeltaPeak fileCap := by
    unfold DirPeakSpec.readFileRuleDeltaLive DirPeakSpec.readFileRuleDeltaPeak
      DirPeakSpec.allocBytes1DeltaLive DirPeakSpec.allocBytes1DeltaPeak
      DirPeakSpec.readFileCliIoDeltaLive DirPeakSpec.readFileCliIoDeltaPeak
    exact max_le_max (Nat.le_refl _) (by decide)
  unfold dirGetRuleDeltaLive dirGetRuleDeltaPeak
    DirPeakSpec.allocBytes1DeltaLive DirPeakSpec.allocBytes1DeltaPeak
  exact max_le_max (Nat.le_refl _) (Nat.add_le_add hp hrf)

private def kutf8 (s : String) : List (BitVec 8) :=
  (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat

private theorem byteArray_toList_eq_data : ∀ (bs : ByteArray), bs.toList = bs.data.toList
  | ⟨⟨xs⟩⟩ => by
    have hloop : ∀ i r, ByteArray.toList.loop ⟨⟨xs⟩⟩ i r = r.reverse ++ xs.drop i := by
      intro i r; fun_induction ByteArray.toList.loop ⟨⟨xs⟩⟩ i r with
      | case1 i r hi ih =>
        have hget : (ByteArray.mk ⟨xs⟩).get! i = xs[i] := getElem!_pos (⟨xs⟩ : Array UInt8) i hi
        rw [ih, hget, List.reverse_cons, List.append_assoc, List.singleton_append,
          List.drop_eq_getElem_cons hi]
      | case2 i r hni => rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hni), List.append_nil]
    exact hloop 0 []

private theorem utf8_eq_kutf8 (s : String) : utf8 s = kutf8 s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [utf8, kutf8, List.utf8Encode, byteArray_toList_eq_data]

theorem utf8_address_length_le : (utf8 "address").length ≤ 7 := by
  have h : (utf8 "address").length = 7 := by rw [utf8_eq_kutf8]; rfl
  omega

theorem utf8_bundleNames_length_le_16 :
    (utf8 "identity-key").length ≤ 16 ∧ (utf8 "registration-id").length ≤ 16 ∧
    (utf8 "signed-pre-key").length ≤ 16 ∧ (utf8 "kyber-pre-key").length ≤ 16 ∧
    (utf8 "one-time-pre-key").length ≤ 16 := by
  have h1 : (utf8 "identity-key").length = 12 := by rw [utf8_eq_kutf8]; rfl
  have h2 : (utf8 "registration-id").length = 15 := by rw [utf8_eq_kutf8]; rfl
  have h3 : (utf8 "signed-pre-key").length = 14 := by rw [utf8_eq_kutf8]; rfl
  have h4 : (utf8 "kyber-pre-key").length = 13 := by rw [utf8_eq_kutf8]; rfl
  have h5 : (utf8 "one-time-pre-key").length = 16 := by rw [utf8_eq_kutf8]; rfl
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

/-! ## `SplitIdEnv`, `SplitSignedEnv`, `addressTryParse`, and `DeserCloneStepEnv` -/

def SplitIdEnv (_file : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  SeqEnv (· = rustAllocEvents 14 1) FreeOnlyEvs evs
def splitIdDeltaCum : Nat := 2 * 14 + 9539
def splitIdDeltaLive : Nat := 14 + 8195
def splitIdDeltaPeak : Nat := 14 + 8195
def splitIdMaxReq : Nat := 14

theorem splitId_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (file : List (BitVec 8)) :
    PhaseCreditSpec M (SplitIdEnv file)
      splitIdDeltaCum splitIdDeltaLive splitIdDeltaPeak splitIdMaxReq :=
  phaseCredit_seq_freeOnly_right hM (PhaseCreditSpec.rustAlloc_aff hM (by decide))
    (fun _ h => h) (Nat.le_refl _)

theorem splitId_small_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsmall : 14 ≤ HasFineReallocCredit.smallMaxReq M) (file : List (BitVec 8)) :
    PhaseCreditSpec M (SplitIdEnv file) splitIdDeltaCum 0 0 splitIdMaxReq :=
  phaseCredit_seq_freeOnly_right hM
    ((PhaseCreditSpec.rustAlloc_small_any hM (al := 1) (by decide) hsmall).mono
      (hM.smallAlloc_le hsmall) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 14))
    (fun _ h => h) (Nat.le_refl 0)

def SplitSignedEnv (file : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  SeqEnv (SplitIdEnv file)
    (fun evs2 => FreeOnlyEvs evs2 ∨ SeqEnv (· = rustAllocEvents 14 1) FreeOnlyEvs evs2) evs
def splitSignedDeltaCum : Nat := 2 * splitIdDeltaCum
def splitSignedDeltaLive : Nat := 2 * splitIdDeltaLive
def splitSignedDeltaPeak : Nat := 2 * splitIdDeltaPeak
def splitSignedMaxReq : Nat := 14

theorem splitSigned_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (file : List (BitVec 8)) :
    PhaseCreditSpec M (SplitSignedEnv file)
      splitSignedDeltaCum splitSignedDeltaLive splitSignedDeltaPeak splitSignedMaxReq := by
  have h1 := splitId_phaseCredit hM file
  exact (h1.seq (phaseCredit_or_freeOnly_left hM (fun _ h => h) h1)).mono
    (by unfold splitSignedDeltaCum; omega) (by unfold splitSignedDeltaLive; omega)
    (by unfold splitSignedDeltaPeak splitIdDeltaLive splitIdDeltaPeak; omega)
    (by unfold splitSignedMaxReq splitIdMaxReq; omega)

theorem splitSigned_small_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsmall : 14 ≤ HasFineReallocCredit.smallMaxReq M) (file : List (BitVec 8)) :
    PhaseCreditSpec M (SplitSignedEnv file) splitSignedDeltaCum 0 0 splitSignedMaxReq := by
  have h1 := splitId_small_phaseCredit hM hsmall file
  exact (h1.seq (phaseCredit_or_freeOnly_left hM (fun _ h => h) h1)).mono
    (by unfold splitSignedDeltaCum; omega) (Nat.le_refl 0) (Nat.le_refl 0)
    (by unfold splitSignedMaxReq splitIdMaxReq; omega)

def addressTryParseDeltaCum : Nat := 2 * 40 + 9539
def addressTryParseDeltaLive : Nat := 40 + 8195
def addressTryParseDeltaPeak : Nat := 40 + 8195
def addressTryParseMaxReq : Nat := 40

theorem addressTryParse_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (bs : List (BitVec 8)) :
    PhaseCreditSpec M (· = addressEvents uuidTryParse bs)
      addressTryParseDeltaCum addressTryParseDeltaLive
      addressTryParseDeltaPeak addressTryParseMaxReq := by
  unfold addressEvents
  cases ha : addrParse uuidTryParse bs with
  | none => exact (PhaseCreditSpec.nil M).mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  | some a =>
    exact (PhaseCreditSpec.rustAlloc_aff hM (by decide)).mono
      (by unfold addressTryParseDeltaCum; have := addrParse_name_length_le ha; omega)
      (by unfold addressTryParseDeltaLive; have := addrParse_name_length_le ha; omega)
      (by unfold addressTryParseDeltaPeak; have := addrParse_name_length_le ha; omega)
      (addrParse_name_length_le ha)

private theorem span_loop_snd_length_le {α : Type} (p : α → Bool) :
    ∀ (xs acc : List α), (List.span.loop p xs acc).2.length ≤ xs.length
  | [], acc => by simp [List.span.loop]
  | x :: xs, acc => by
    unfold List.span.loop
    split
    · exact Nat.le_trans (span_loop_snd_length_le p xs (x :: acc)) (Nat.le_succ _)
    · exact Nat.le_refl _

theorem addrParse_name_lt_length (uuidParse : UuidParser) {bs : List (BitVec 8)} {a : AddrV}
    (h : addrParse uuidParse bs = some a) : a.name.length < bs.length := by
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
        | cons _ nameR =>
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
      · dsimp only at h; split_ifs at h; injection h with ha; rw [← ha]; exact hlt

theorem addressEvents_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (uuidParse : UuidParser) (bs : List (BitVec 8)) :
    PhaseCreditSpec M (· = addressEvents uuidParse bs)
      (2 * bs.length + 9539) (bs.length + 8195) (bs.length + 8195) bs.length := by
  unfold addressEvents
  cases ha : addrParse uuidParse bs with
  | none =>
    exact (PhaseCreditSpec.nil M).mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  | some a =>
    have hlt := addrParse_name_lt_length uuidParse ha
    exact (PhaseCreditSpec.rustAlloc_aff hM (req := a.name.length) (al := 1) (by decide)).mono
      (by omega) (by omega) (by omega) (Nat.le_of_lt hlt)

def KemDeserStepEnv (evs : List AllocEvent) : Prop := evs = rustAllocEvents kemPkLen 1 ∨ evs = []

theorem kemDeserStepEnv_of_kemDeserializeEvents (bs : List (BitVec 8)) :
    KemDeserStepEnv (kemDeserializeEvents bs) := by
  unfold kemDeserializeEvents; split <;> [exact Or.inl rfl; exact Or.inr rfl]

theorem kemDeserStep_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M) :
    PhaseCreditSpec M KemDeserStepEnv
      (2 * kemPkLen + 9539) (kemPkLen + 8195) (kemPkLen + 8195) kemPkLen :=
  ((PhaseCreditSpec.rustAlloc_aff hM (by decide)).or (PhaseCreditSpec.nil M)).mono
    (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.zero_le _⟩) (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.zero_le _⟩)
    (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.zero_le _⟩) (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.zero_le _⟩)

def DeserCloneStepEnv (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨ SeqEnv (· = rustAllocEvents 64 1) (SeqEnv KemDeserStepEnv
    (fun evs3 => FreeOnlyEvs evs3 ∨ SeqEnv (· = rustAllocEvents 64 1) FreeOnlyEvs evs3)) evs
def deserCloneDeltaCum : Nat := 2 * (2 * 64 + 9539) + (2 * kemPkLen + 9539)
def deserCloneDeltaLive : Nat := 2 * (64 + 8195) + (kemPkLen + 8195)
def deserCloneDeltaPeak : Nat := 2 * (64 + 8195) + (kemPkLen + 8195)
def deserCloneMaxReq : Nat := max 64 kemPkLen

theorem deserCloneStep_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) :
    PhaseCreditSpec M DeserCloneStepEnv
      deserCloneDeltaCum deserCloneDeltaLive deserCloneDeltaPeak deserCloneMaxReq := by
  have h64 := PhaseCreditSpec.rustAlloc_aff hM (req := 64) (al := 1) (by decide)
  have h64Opt := phaseCredit_or_freeOnly_left hM (fun _ h => h)
    (phaseCredit_seq_freeOnly_right hM h64 (fun _ h => h) (Nat.le_refl _))
  have hmain : PhaseCreditSpec M _
      deserCloneDeltaCum deserCloneDeltaLive deserCloneDeltaPeak deserCloneMaxReq :=
    (h64.seq ((kemDeserStep_phaseCredit hM).seq h64Opt)).mono
      (by unfold deserCloneDeltaCum; generalize kemPkLen = k; omega)
      (by unfold deserCloneDeltaLive; generalize kemPkLen = k; omega)
      (by unfold deserCloneDeltaPeak; generalize kemPkLen = k; omega)
      (by unfold deserCloneMaxReq; generalize kemPkLen = k; omega)
  exact phaseCredit_or_freeOnly_left hM (fun _ h => h) hmain

/-! ## `BundleReadEnv` and LIFO Temporary-File Cancellation (`TempFileBracketEnv`) -/

def errStr22DeltaCum : Nat := 2 * 22 + 9539
def errStr22DeltaLive : Nat := 22 + 8195
def errStr22DeltaPeak : Nat := 22 + 8195

def BundleReadPostPathEnv (rd : ReadRule) (files : FsFiles) (fullPath : List (BitVec 8))
    (evs : List AllocEvent) : Prop :=
  match rd files fullPath with
  | .ok bs => ConcatEnv (· = allocBytes1Events bs) FreeOnlyEvs evs
  | .error () => SeqEnv FreeOnlyEvs (· = rustAllocEvents 22 1) evs

def BundleReadEnv (rd : ReadRule) (files : FsFiles) (dir name : List (BitVec 8))
    (evs : List AllocEvent) : Prop :=
  SeqEnv (CliPathEnv dir name) (BundleReadPostPathEnv rd files (pathOf dir name)) evs

def bundleReadPostDeltaCum (fileCap : Nat) : Nat := 2 * max 22 fileCap + 9539
def bundleReadPostDeltaLive (fileCap : Nat) : Nat := max 22 fileCap + 8195
def bundleReadPostDeltaPeak (fileCap : Nat) : Nat := max 22 fileCap + 8195
def bundleReadPostMaxReq (fileCap : Nat) : Nat := max 22 fileCap

theorem bundleReadPost_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (rd : ReadRule) (files : FsFiles) (fullPath : List (BitVec 8))
    {fileCap : Nat} (hcap : ∀ bs, rd files fullPath = .ok bs → bs.length ≤ fileCap) :
    PhaseCreditSpec M (BundleReadPostPathEnv rd files fullPath)
      (bundleReadPostDeltaCum fileCap) (bundleReadPostDeltaLive fileCap)
      (bundleReadPostDeltaPeak fileCap) (bundleReadPostMaxReq fileCap) := by
  unfold BundleReadPostPathEnv; split
  · rename_i bs heq
    have hbs := Nat.le_trans (hcap bs heq) (Nat.le_max_right 22 fileCap)
    exact (phaseCredit_seq_freeOnly_right hM
      (phaseCredit_allocBytes1OfLen_aff hM hbs) (fun _ h => h) (Nat.le_refl _)).of_imp
      (fun _ hc => hc.toSeqEnv)
  · have h22 : PhaseCreditSpec M (· = rustAllocEvents 22 1)
        (bundleReadPostDeltaCum fileCap) (bundleReadPostDeltaLive fileCap)
        (bundleReadPostDeltaPeak fileCap) (bundleReadPostMaxReq fileCap) :=
      (PhaseCreditSpec.rustAlloc_aff hM (req := 22) (al := 1) (by decide)).mono
        (by unfold bundleReadPostDeltaCum; omega) (by unfold bundleReadPostDeltaLive; omega)
        (by unfold bundleReadPostDeltaPeak; omega) (Nat.le_max_left 22 fileCap)
    exact phaseCredit_seq_freeOnly_left hM (fun _ h => h) h22

theorem bundleRead_phaseCredit_of_path {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {rd : ReadRule} {files : FsFiles} {dir name : List (BitVec 8)}
    {c_p l_p p_p r_p fileCap : Nat} (hpath : PhaseCreditSpec M (CliPathEnv dir name) c_p l_p p_p r_p)
    (hcap : ∀ bs, rd files (pathOf dir name) = .ok bs → bs.length ≤ fileCap) :
    PhaseCreditSpec M (BundleReadEnv rd files dir name)
      (c_p + bundleReadPostDeltaCum fileCap) (l_p + bundleReadPostDeltaLive fileCap)
      (max p_p (l_p + bundleReadPostDeltaPeak fileCap)) (max r_p (bundleReadPostMaxReq fileCap)) :=
  hpath.seq (bundleReadPost_phaseCredit hM rd files (pathOf dir name) hcap)

theorem bundleRead_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {rd : ReadRule} {files : FsFiles} {dir name : List (BitVec 8)}
    {maxDir maxName fileCap : Nat} (hdir : dir.length ≤ maxDir) (hname : name.length ≤ maxName)
    (hcap : ∀ bs, rd files (pathOf dir name) = .ok bs → bs.length ≤ fileCap) :
    PhaseCreditSpec M (BundleReadEnv rd files dir name)
      (pathDeltaCum maxDir maxName + bundleReadPostDeltaCum fileCap)
      (pathDeltaLive maxDir maxName + bundleReadPostDeltaLive fileCap)
      (max (pathDeltaPeak maxDir maxName)
        (pathDeltaLive maxDir maxName + bundleReadPostDeltaPeak fileCap))
      (max (pathMaxReq maxDir maxName) (bundleReadPostMaxReq fileCap)) :=
  bundleRead_phaseCredit_of_path hM (path_phaseCredit hM hdir hname) hcap

/-- Exact-order LIFO temporary-file bracket cancelling `bs` out of post-bracket `Δlive`. -/
def TempFileBracketEnv (rd : ReadRule) (files : FsFiles) (dir name : List (BitVec 8))
    (Body : List (BitVec 8) → List AllocEvent → Prop) (evs : List AllocEvent) : Prop :=
  SeqEnv (CliPathEnv dir name)
    (match rd files (pathOf dir name) with
     | .error () => fun evs2 =>
       FreeOnlyEvs evs2 ∨ SeqEnv FreeOnlyEvs (SeqEnv (· = rustAllocEvents 22 1) FreeOnlyEvs) evs2
     | .ok bs => SeqEnv (ConcatEnv
       (ConcatEnv (· = allocBytes1Events bs) (SeqEnv FreeOnlyEvs (Body bs)))
       (· = deallocBytes1OfLen bs.length)) FreeOnlyEvs) evs

theorem tempFileBracketEnv_of_bundleRead {rd : ReadRule} {files : FsFiles}
    {dir name : List (BitVec 8)} {Body : List (BitVec 8) → List AllocEvent → Prop}
    {evs : List AllocEvent}
    (h : ConcatEnv
      (ConcatEnv (CliPathEnv dir name) (BundleReadPostPathEnv rd files (pathOf dir name)))
      (match rd files (pathOf dir name) with
       | .error () => FreeOnlyEvs
       | .ok bs =>
         ConcatEnv (Body bs) (ConcatEnv (· = deallocBytes1OfLen bs.length) FreeOnlyEvs)) evs) :
    TempFileBracketEnv rd files dir name Body evs := by
  obtain ⟨_, evs_rest, rfl, ⟨evs_p, evs_post, rfl, hp, hpost⟩, hrest⟩ := h
  refine Or.inr ⟨evs_p, evs_post ++ evs_rest, List.append_assoc _ _ _, hp, ?_⟩
  unfold BundleReadPostPathEnv at hpost
  cases hrd : rd files (pathOf dir name) with
  | error u =>
    rw [hrd] at hpost hrest
    rcases hpost with hf | ⟨evs_f, evs_22, rfl, hf, rfl⟩
    · exact Or.inl (freeOnlyEvs_of_seqEnv (fun _ h => h) (fun _ h => h)
        (Or.inr ⟨evs_post, evs_rest, rfl, hf, hrest⟩))
    · exact Or.inr (Or.inr ⟨evs_f, rustAllocEvents 22 1 ++ evs_rest, List.append_assoc _ _ _, hf,
        Or.inr ⟨rustAllocEvents 22 1, evs_rest, rfl, rfl, hrest⟩⟩)
  | ok bs =>
    rw [hrd] at hpost hrest
    obtain ⟨_, evs_pf, rfl, rfl, hpf⟩ := hpost
    obtain ⟨evs_b, _, rfl, hb, ⟨_, evs_t, rfl, rfl, ht⟩⟩ := hrest
    refine Or.inr ⟨(allocBytes1Events bs ++ (evs_pf ++ evs_b)) ++ deallocBytes1OfLen bs.length,
      evs_t, by simp only [List.append_assoc], ?_, ht⟩
    exact ⟨allocBytes1Events bs ++ (evs_pf ++ evs_b), deallocBytes1OfLen bs.length, rfl,
      ⟨allocBytes1Events bs, evs_pf ++ evs_b, rfl, rfl, Or.inr ⟨evs_pf, evs_b, rfl, hpf, hb⟩⟩, rfl⟩

def tempFilePostCum (fileCap c_b : Nat) : Nat := max errStr22DeltaCum (2 * fileCap + 9539 + c_b)
def tempFilePostLive (l_b : Nat) : Nat := max errStr22DeltaLive l_b
def tempFilePostPeak (fileCap p_b : Nat) : Nat := max errStr22DeltaPeak (fileCap + 8195 + p_b)
def tempFilePostMaxReq (fileCap r_b : Nat) : Nat := max 22 (max fileCap r_b)

theorem tempFilePostLive_le_peak {fileCap l_b p_b : Nat} (hlp : l_b ≤ p_b) :
    tempFilePostLive l_b ≤ tempFilePostPeak fileCap p_b := max_le_max (Nat.le_refl _) (by omega)

private theorem bracket_lp {l_p l_b p_p fileCap p_b : Nat} (hlp : l_b ≤ p_b) :
    l_p + tempFilePostLive l_b ≤ max p_p (l_p + tempFilePostPeak fileCap p_b) :=
  Nat.le_trans (Nat.add_le_add_left (tempFilePostLive_le_peak hlp) l_p) (Nat.le_max_right _ _)

theorem tempFileBracket_phaseCredit_of_path {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {rd : ReadRule} {files : FsFiles} {dir name : List (BitVec 8)}
    {Body : List (BitVec 8) → List AllocEvent → Prop} {c_p l_p p_p r_p fileCap c_b l_b p_b r_b : Nat}
    (hpath : PhaseCreditSpec M (CliPathEnv dir name) c_p l_p p_p r_p)
    (hcap : ∀ bs, rd files (pathOf dir name) = .ok bs → bs.length ≤ fileCap)
    (hbody : ∀ bs, bs.length ≤ fileCap → PhaseCreditSpec M (Body bs) c_b l_b p_b r_b)
    (hlp_b : l_b ≤ p_b) :
    PhaseCreditSpec M (TempFileBracketEnv rd files dir name Body)
      (c_p + tempFilePostCum fileCap c_b) (l_p + tempFilePostLive l_b)
      (max p_p (l_p + tempFilePostPeak fileCap p_b)) (max r_p (tempFilePostMaxReq fileCap r_b)) := by
  refine hpath.seq ?_
  cases hrd : rd files (pathOf dir name) with
  | error u =>
    have h22 := phaseCredit_seq_freeOnly_right hM
      (PhaseCreditSpec.rustAlloc_aff hM (req := 22) (al := 1) (by decide)) (fun _ h => h) (Nat.le_refl _)
    exact (phaseCredit_or_freeOnly_left hM (fun _ h => h)
      (phaseCredit_seq_freeOnly_left hM (fun _ h => h) h22)).mono
      (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  | ok bs =>
    have hbs := hcap bs hrd
    have hcancel := phaseCredit_tempAllocBytes1BodyFree_le hM hbs
      (phaseCredit_seq_freeOnly_left hM (fun _ h => h) (hbody bs hbs))
    exact (phaseCredit_seq_freeOnly_right hM hcancel (fun _ h => h) (by omega)).mono
      (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _)

theorem tempFileBracket_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {rd : ReadRule} {files : FsFiles} {dir name : List (BitVec 8)}
    {Body : List (BitVec 8) → List AllocEvent → Prop}
    {maxDir maxName fileCap c_b l_b p_b r_b : Nat}
    (hdir : dir.length ≤ maxDir) (hname : name.length ≤ maxName)
    (hcap : ∀ bs, rd files (pathOf dir name) = .ok bs → bs.length ≤ fileCap)
    (hbody : ∀ bs, bs.length ≤ fileCap → PhaseCreditSpec M (Body bs) c_b l_b p_b r_b)
    (hlp_b : l_b ≤ p_b) :
    PhaseCreditSpec M (TempFileBracketEnv rd files dir name Body)
      (pathDeltaCum maxDir maxName + tempFilePostCum fileCap c_b)
      (pathDeltaLive maxDir maxName + tempFilePostLive l_b)
      (max (pathDeltaPeak maxDir maxName)
        (pathDeltaLive maxDir maxName + tempFilePostPeak fileCap p_b))
      (max (pathMaxReq maxDir maxName) (tempFilePostMaxReq fileCap r_b)) :=
  tempFileBracket_phaseCredit_of_path hM (path_phaseCredit hM hdir hname) hcap hbody hlp_b

/-! ## Prologue `R0` and `.init` Arm (`R1a → R1b → R1c`) -/

def R0PostGetEnv (uuidParse : UuidParser) (ownB : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨ SeqEnv (· = addressEvents uuidParse ownB)
    (SeqEnv (fun e => e = deallocBytes1OfLen ownB.length) FreeOnlyEvs) evs

def R0Env (uuidParse : UuidParser) (rd : ReadRule) (files : FsFiles) (ownDir : DirGhost)
    (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨ SeqEnv (CliDirGetEnv (ReadFileRuleEnv rd) files ownDir (utf8 "address"))
    (match ownDir.get rd files (utf8 "address") with
     | .error () => FreeOnlyEvs
     | .ok ownB => R0PostGetEnv uuidParse ownB) evs

def R0OpenedEnv (rd : ReadRule) (files : FsFiles) (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨ TempFileBracketEnv rd files StoresGhost.opened.identity.own.path (utf8 "address")
    (fun ownB evs_b => FreeOnlyEvs evs_b ∨ evs_b = addressEvents uuidTryParse ownB) evs

theorem r0PostGet_tryParse_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (ownB : List (BitVec 8)) :
    PhaseCreditSpec M (R0PostGetEnv uuidTryParse ownB)
      addressTryParseDeltaCum addressTryParseDeltaLive
      addressTryParseDeltaPeak addressTryParseMaxReq :=
  phaseCredit_or_freeOnly_left hM (fun _ h => h)
    (phaseCredit_seq_freeOnly_right hM (addressTryParse_phaseCredit hM ownB)
      (freeOnlyEvs_seq_deallocBytes1OfLen ownB.length) (Nat.le_refl _))

theorem r0_tryParse_phaseCredit_of_dirGet {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {rd : ReadRule} {files : FsFiles} {ownDir : DirGhost} {c_g l_g p_g r_g : Nat}
    (hget : PhaseCreditSpec M
      (CliDirGetEnv (ReadFileRuleEnv rd) files ownDir (utf8 "address")) c_g l_g p_g r_g) :
    PhaseCreditSpec M (R0Env uuidTryParse rd files ownDir)
      (c_g + addressTryParseDeltaCum) (l_g + addressTryParseDeltaLive)
      (max p_g (l_g + addressTryParseDeltaPeak)) (max r_g addressTryParseMaxReq) := by
  have hpost : PhaseCreditSpec M
      (match ownDir.get rd files (utf8 "address") with
       | .error () => FreeOnlyEvs | .ok ownB => R0PostGetEnv uuidTryParse ownB)
      addressTryParseDeltaCum addressTryParseDeltaLive
      addressTryParseDeltaPeak addressTryParseMaxReq := by
    cases ownDir.get rd files (utf8 "address") with
    | error _ =>
      exact (PhaseCreditSpec.freeOnly_of_hyps hM).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    | ok ownB => exact r0PostGet_tryParse_phaseCredit hM ownB
  exact phaseCredit_or_freeOnly_left hM (fun _ h => h) (hget.seq hpost)

theorem r0Opened_phaseCredit_of_path {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {rd : ReadRule} {files : FsFiles} {c_p l_p p_p r_p fileCap : Nat}
    (hpath : PhaseCreditSpec M
      (CliPathEnv StoresGhost.opened.identity.own.path (utf8 "address")) c_p l_p p_p r_p)
    (hcap : ∀ bs,
      rd files (pathOf StoresGhost.opened.identity.own.path (utf8 "address")) = .ok bs →
      bs.length ≤ fileCap) :
    PhaseCreditSpec M (R0OpenedEnv rd files)
      (c_p + tempFilePostCum fileCap addressTryParseDeltaCum)
      (l_p + tempFilePostLive addressTryParseDeltaLive)
      (max p_p (l_p + tempFilePostPeak fileCap addressTryParseDeltaPeak))
      (max r_p (tempFilePostMaxReq fileCap addressTryParseMaxReq)) :=
  phaseCredit_or_freeOnly_left hM (fun _ h => h)
    (tempFileBracket_phaseCredit_of_path hM hpath hcap
      (fun ownB _ => phaseCredit_or_freeOnly_left hM (fun _ h => h)
        (addressTryParse_phaseCredit hM ownB)) (Nat.le_refl _))

def R1aEnv (rd : ReadRule) (files : FsFiles) (dir : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨ TempFileBracketEnv rd files dir (utf8 "identity-key") (fun _ => FreeOnlyEvs) evs
def r1aDeltaCum (c_p fileCap : Nat) : Nat := c_p + tempFilePostCum fileCap 0
def r1aDeltaLive (l_p : Nat) : Nat := l_p + tempFilePostLive 0
def r1aDeltaPeak (l_p p_p fileCap : Nat) : Nat := max p_p (l_p + tempFilePostPeak fileCap 0)
def r1aMaxReq (r_p fileCap : Nat) : Nat := max r_p (tempFilePostMaxReq fileCap 0)

theorem r1a_phaseCredit_of_path {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {rd : ReadRule} {files : FsFiles} {dir : List (BitVec 8)}
    {c_p l_p p_p r_p fileCap : Nat}
    (hpath : PhaseCreditSpec M (CliPathEnv dir (utf8 "identity-key")) c_p l_p p_p r_p)
    (hcap : ∀ bs, rd files (pathOf dir (utf8 "identity-key")) = .ok bs → bs.length ≤ fileCap) :
    PhaseCreditSpec M (R1aEnv rd files dir)
      (r1aDeltaCum c_p fileCap) (r1aDeltaLive l_p)
      (r1aDeltaPeak l_p p_p fileCap) (r1aMaxReq r_p fileCap) :=
  phaseCredit_or_freeOnly_left hM (fun _ h => h)
    (tempFileBracket_phaseCredit_of_path hM hpath hcap
      (fun _ _ => PhaseCreditSpec.freeOnly_of_hyps hM) (Nat.le_refl 0))

def R1bOpkDeserStageEnv (rd : ReadRule) (files : FsFiles) (dir : List (BitVec 8))
    (evs : List AllocEvent) : Prop :=
  SeqEnv (TempFileBracketEnv rd files dir (utf8 "one-time-pre-key")
    (fun opkBs evs_o => FreeOnlyEvs evs_o ∨ SplitIdEnv opkBs evs_o)) DeserCloneStepEnv evs

def R1bKpkStageEnv (rd : ReadRule) (files : FsFiles) (dir : List (BitVec 8))
    (evs : List AllocEvent) : Prop :=
  TempFileBracketEnv rd files dir (utf8 "kyber-pre-key") (fun kpkBs evs_k =>
    SeqEnv (SplitSignedEnv kpkBs)
      (fun evs_k2 => FreeOnlyEvs evs_k2 ∨ R1bOpkDeserStageEnv rd files dir evs_k2) evs_k) evs

def R1bSpkStageEnv (rd : ReadRule) (files : FsFiles) (dir : List (BitVec 8))
    (evs : List AllocEvent) : Prop :=
  TempFileBracketEnv rd files dir (utf8 "signed-pre-key") (fun spkBs evs_s =>
    SeqEnv (SplitSignedEnv spkBs)
      (fun evs_s2 => FreeOnlyEvs evs_s2 ∨ R1bKpkStageEnv rd files dir evs_s2) evs_s) evs

/-- Full exact-order `R1b` bundle-read & key-deserialize envelope cancelling all 4 bundle buffers. -/
def R1bEnv (rd : ReadRule) (files : FsFiles) (dir : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  TempFileBracketEnv rd files dir (utf8 "registration-id") (fun regBs evs_r =>
    FreeOnlyEvs evs_r ∨ (SplitIdEnv regBs evs_r ∨ R1bSpkStageEnv rd files dir evs_r)) evs

def r1bOpkDeserCum (c_p fileCap : Nat) : Nat :=
  (c_p + tempFilePostCum fileCap splitIdDeltaCum) + deserCloneDeltaCum
def r1bOpkDeserLive (l_p : Nat) : Nat :=
  (l_p + tempFilePostLive splitIdDeltaLive) + deserCloneDeltaLive
def r1bOpkDeserPeak (l_p p_p fileCap : Nat) : Nat :=
  max (max p_p (l_p + tempFilePostPeak fileCap splitIdDeltaPeak))
    ((l_p + tempFilePostLive splitIdDeltaLive) + deserCloneDeltaPeak)
def r1bOpkDeserMaxReq (r_p fileCap : Nat) : Nat :=
  max (max r_p (tempFilePostMaxReq fileCap splitIdMaxReq)) deserCloneMaxReq

def r1bKpkCum (c_p fileCap : Nat) : Nat :=
  c_p + tempFilePostCum fileCap (splitSignedDeltaCum + r1bOpkDeserCum c_p fileCap)
def r1bKpkLive (l_p : Nat) : Nat :=
  l_p + tempFilePostLive (splitSignedDeltaLive + r1bOpkDeserLive l_p)
def r1bKpkPeak (l_p p_p fileCap : Nat) : Nat :=
  max p_p (l_p + tempFilePostPeak fileCap
    (max splitSignedDeltaPeak (splitSignedDeltaLive + r1bOpkDeserPeak l_p p_p fileCap)))
def r1bKpkMaxReq (r_p fileCap : Nat) : Nat :=
  max r_p (tempFilePostMaxReq fileCap (max splitSignedMaxReq (r1bOpkDeserMaxReq r_p fileCap)))

def r1bSpkCum (c_p fileCap : Nat) : Nat :=
  c_p + tempFilePostCum fileCap (splitSignedDeltaCum + r1bKpkCum c_p fileCap)
def r1bSpkLive (l_p : Nat) : Nat :=
  l_p + tempFilePostLive (splitSignedDeltaLive + r1bKpkLive l_p)
def r1bSpkPeak (l_p p_p fileCap : Nat) : Nat :=
  max p_p (l_p + tempFilePostPeak fileCap
    (max splitSignedDeltaPeak (splitSignedDeltaLive + r1bKpkPeak l_p p_p fileCap)))
def r1bSpkMaxReq (r_p fileCap : Nat) : Nat :=
  max r_p (tempFilePostMaxReq fileCap (max splitSignedMaxReq (r1bKpkMaxReq r_p fileCap)))

def r1bDeltaCum (c_p fileCap : Nat) : Nat :=
  c_p + tempFilePostCum fileCap (max splitIdDeltaCum (r1bSpkCum c_p fileCap))
def r1bDeltaLive (l_p : Nat) : Nat :=
  l_p + tempFilePostLive (max splitIdDeltaLive (r1bSpkLive l_p))
def r1bDeltaPeak (l_p p_p fileCap : Nat) : Nat :=
  max p_p (l_p + tempFilePostPeak fileCap (max splitIdDeltaPeak (r1bSpkPeak l_p p_p fileCap)))
def r1bMaxReq (r_p fileCap : Nat) : Nat :=
  max r_p (tempFilePostMaxReq fileCap (max splitIdMaxReq (r1bSpkMaxReq r_p fileCap)))

theorem r1bDeltaLive_le_peak (l_p p_p fileCap : Nat) :
    r1bDeltaLive l_p ≤ r1bDeltaPeak l_p p_p fileCap := by
  have hopk : r1bOpkDeserLive l_p ≤ r1bOpkDeserPeak l_p p_p fileCap := Nat.le_max_right _ _
  have hkpk : r1bKpkLive l_p ≤ r1bKpkPeak l_p p_p fileCap :=
    bracket_lp (Nat.le_trans (Nat.add_le_add_left hopk _) (Nat.le_max_right _ _))
  have hspk : r1bSpkLive l_p ≤ r1bSpkPeak l_p p_p fileCap :=
    bracket_lp (Nat.le_trans (Nat.add_le_add_left hkpk _) (Nat.le_max_right _ _))
  exact bracket_lp (max_le_max (Nat.le_refl _) hspk)

theorem r1b_phaseCredit_of_paths {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {rd : ReadRule} {files : FsFiles} {dir : List (BitVec 8)}
    {c_p l_p p_p r_p fileCap : Nat}
    (hpathReg : PhaseCreditSpec M (CliPathEnv dir (utf8 "registration-id")) c_p l_p p_p r_p)
    (hpathSpk : PhaseCreditSpec M (CliPathEnv dir (utf8 "signed-pre-key")) c_p l_p p_p r_p)
    (hpathKpk : PhaseCreditSpec M (CliPathEnv dir (utf8 "kyber-pre-key")) c_p l_p p_p r_p)
    (hpathOpk : PhaseCreditSpec M (CliPathEnv dir (utf8 "one-time-pre-key")) c_p l_p p_p r_p)
    (hcap : ∀ name bs, rd files (pathOf dir name) = .ok bs → bs.length ≤ fileCap) :
    PhaseCreditSpec M (R1bEnv rd files dir)
      (r1bDeltaCum c_p fileCap) (r1bDeltaLive l_p)
      (r1bDeltaPeak l_p p_p fileCap) (r1bMaxReq r_p fileCap) := by
  have hopkBr := tempFileBracket_phaseCredit_of_path hM hpathOpk (fun bs hr => hcap _ bs hr)
    (fun opkBs _ => phaseCredit_or_freeOnly_left hM (fun _ h => h) (splitId_phaseCredit hM opkBs))
    (Nat.le_refl _)
  have hopkDeser : PhaseCreditSpec M (R1bOpkDeserStageEnv rd files dir)
      (r1bOpkDeserCum c_p fileCap) (r1bOpkDeserLive l_p)
      (r1bOpkDeserPeak l_p p_p fileCap) (r1bOpkDeserMaxReq r_p fileCap) :=
    hopkBr.seq (deserCloneStep_phaseCredit hM)
  have hopkLp : r1bOpkDeserLive l_p ≤ r1bOpkDeserPeak l_p p_p fileCap := Nat.le_max_right _ _
  have hkpkStage : PhaseCreditSpec M (R1bKpkStageEnv rd files dir)
      (r1bKpkCum c_p fileCap) (r1bKpkLive l_p)
      (r1bKpkPeak l_p p_p fileCap) (r1bKpkMaxReq r_p fileCap) :=
    tempFileBracket_phaseCredit_of_path hM hpathKpk (fun bs hr => hcap _ bs hr)
      (fun kpkBs _ => (splitSigned_phaseCredit hM kpkBs).seq
        (phaseCredit_or_freeOnly_left hM (fun _ h => h) hopkDeser))
      (Nat.le_trans (Nat.add_le_add_left hopkLp _) (Nat.le_max_right _ _))
  have hkpkLp : r1bKpkLive l_p ≤ r1bKpkPeak l_p p_p fileCap :=
    bracket_lp (Nat.le_trans (Nat.add_le_add_left hopkLp _) (Nat.le_max_right _ _))
  have hspkStage : PhaseCreditSpec M (R1bSpkStageEnv rd files dir)
      (r1bSpkCum c_p fileCap) (r1bSpkLive l_p)
      (r1bSpkPeak l_p p_p fileCap) (r1bSpkMaxReq r_p fileCap) :=
    tempFileBracket_phaseCredit_of_path hM hpathSpk (fun bs hr => hcap _ bs hr)
      (fun spkBs _ => (splitSigned_phaseCredit hM spkBs).seq
        (phaseCredit_or_freeOnly_left hM (fun _ h => h) hkpkStage))
      (Nat.le_trans (Nat.add_le_add_left hkpkLp _) (Nat.le_max_right _ _))
  have hspkLp : r1bSpkLive l_p ≤ r1bSpkPeak l_p p_p fileCap :=
    bracket_lp (Nat.le_trans (Nat.add_le_add_left hkpkLp _) (Nat.le_max_right _ _))
  exact tempFileBracket_phaseCredit_of_path hM hpathReg (fun bs hr => hcap _ bs hr)
    (fun regBs _ => phaseCredit_or_freeOnly_left hM (fun _ h => h)
      ((splitId_phaseCredit hM regBs).or hspkStage))
    (max_le_max (Nat.le_refl _) hspkLp)

def R1cEnv (InitEnv : List AllocEvent → Prop) (evs : List AllocEvent) : Prop :=
  SeqEnv InitEnv FreeOnlyEvs evs

theorem r1c_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {InitEnv : List AllocEvent → Prop} {c_i l_i p_i r_i : Nat}
    (hinit : PhaseCreditSpec M InitEnv c_i l_i p_i r_i) (hlp_i : l_i ≤ p_i) :
    PhaseCreditSpec M (R1cEnv InitEnv) c_i l_i p_i r_i :=
  phaseCredit_seq_freeOnly_right hM hinit (fun _ h => h) hlp_i

def InitArmEnv (rd : ReadRule) (files : FsFiles) (dir : List (BitVec 8))
    (InitEnv : List AllocEvent → Prop) (evs : List AllocEvent) : Prop :=
  SeqEnv (R1aEnv rd files dir) (fun evs1 => FreeOnlyEvs evs1 ∨
    SeqEnv (R1bEnv rd files dir) (fun evs2 => FreeOnlyEvs evs2 ∨ R1cEnv InitEnv evs2) evs1) evs
def initArmDeltaCum (c_p fileCap c_i : Nat) : Nat :=
  r1aDeltaCum c_p fileCap + (r1bDeltaCum c_p fileCap + c_i)
def initArmDeltaLive (l_p l_i : Nat) : Nat := r1aDeltaLive l_p + (r1bDeltaLive l_p + l_i)
def initArmDeltaPeak (l_p p_p fileCap p_i : Nat) : Nat :=
  max (r1aDeltaPeak l_p p_p fileCap)
    (r1aDeltaLive l_p + max (r1bDeltaPeak l_p p_p fileCap) (r1bDeltaLive l_p + p_i))
def initArmMaxReq (r_p fileCap r_i : Nat) : Nat :=
  max (r1aMaxReq r_p fileCap) (max (r1bMaxReq r_p fileCap) r_i)

theorem initArm_phaseCredit_of_paths {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {rd : ReadRule} {files : FsFiles} {dir : List (BitVec 8)}
    {InitEnv : List AllocEvent → Prop} {c_p l_p p_p r_p fileCap c_i l_i p_i r_i : Nat}
    (hpathIk : PhaseCreditSpec M (CliPathEnv dir (utf8 "identity-key")) c_p l_p p_p r_p)
    (hpathReg : PhaseCreditSpec M (CliPathEnv dir (utf8 "registration-id")) c_p l_p p_p r_p)
    (hpathSpk : PhaseCreditSpec M (CliPathEnv dir (utf8 "signed-pre-key")) c_p l_p p_p r_p)
    (hpathKpk : PhaseCreditSpec M (CliPathEnv dir (utf8 "kyber-pre-key")) c_p l_p p_p r_p)
    (hpathOpk : PhaseCreditSpec M (CliPathEnv dir (utf8 "one-time-pre-key")) c_p l_p p_p r_p)
    (hcap : ∀ name bs, rd files (pathOf dir name) = .ok bs → bs.length ≤ fileCap)
    (hinit : PhaseCreditSpec M InitEnv c_i l_i p_i r_i) (hlp_i : l_i ≤ p_i) :
    PhaseCreditSpec M (InitArmEnv rd files dir InitEnv)
      (initArmDeltaCum c_p fileCap c_i) (initArmDeltaLive l_p l_i)
      (initArmDeltaPeak l_p p_p fileCap p_i) (initArmMaxReq r_p fileCap r_i) :=
  (r1a_phaseCredit_of_path hM hpathIk (fun bs hr => hcap _ bs hr)).seq
    (phaseCredit_or_freeOnly_left hM (fun _ h => h)
      ((r1b_phaseCredit_of_paths hM hpathReg hpathSpk hpathKpk hpathOpk hcap).seq
        (phaseCredit_or_freeOnly_left hM (fun _ h => h) (r1c_phaseCredit hM hinit hlp_i))))

/-! ## `.send` (`R2`), `.recv` (`R3a | R3b | RecvBad`), and Join (`J`) -/

/-- Maximum `cumSmall` charge of a single `al ≤ 16` allocation across all request sizes on
`fineCostModel` (`135,167 + 8,195 + 122 = 143,484` B). -/
def maxTryCloneSmallBytes : Nat := 143484

/-- Tight single-allocation `cumSmall` cap hypothesis (`smallAllocCost M r ≤ 143,484` for all
`r ≤ smallMaxReq M`), discharged on `fineCostModel` by `fineCostModel_cliRunTightHyps`. -/
structure CliRunTightHyps (M : AllocCostModel) [HasFineReallocCredit M] : Prop where
  hSmallAllocCap : ∀ r, r ≤ HasFineReallocCredit.smallMaxReq M →
    HasFineReallocCredit.smallAllocCost M r ≤ maxTryCloneSmallBytes

private theorem grp_extra_le_366 {g s : Nat} (hs : 0 < s) (hg : g ≤ 3 * s) :
    (122 * g + s - 1) / s ≤ 366 := by
  have hmul : 122 * g ≤ 366 * s := by
    calc 122 * g ≤ 122 * (3 * s) := Nat.mul_le_mul_left 122 hg
      _ = 366 * s := (Nat.mul_assoc 122 3 s).symm
  exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hs).mpr (by omega))

theorem fineCostModel_cliRunTightHyps : CliRunTightHyps fineCostModel where
  hSmallAllocCap r hr := by
    rw [fineCostModel_smallMaxReq_eq] at hr
    change fineSmallAllocCost r ≤ maxTryCloneSmallBytes
    unfold fineSmallAllocCost
    by_cases hm : r ≤ MmapThresholdReq
    · simp only [hm, ↓reduceIte]
      obtain ⟨hSlot, hGrp⟩ := coarseWt_le_cap (sizeToClassUnits ((r + 3) / 16))
      exact Nat.le_trans
        (Nat.add_le_add hSlot (grp_extra_le_366 (by unfold FineScale; decide) hGrp))
        (by unfold maxTryCloneSmallBytes; decide)
    · simp only [hm, ↓reduceIte]
      have hlg : fineLargeCost r = r + 8195 := fineCostModel_largeCost_eq r
      unfold fineLargeCost at hlg
      rw [hlg]
      exact Nat.le_trans
        (Nat.add_le_add_right (Nat.add_le_add_right hr 8195) 122)
        (by unfold maxTryCloneSmallBytes; decide)

theorem tryCloneSmallDelta_eq_bytesCumAlloc (M : AllocCostModel) [HasFineReallocCredit M]
    (n : Nat) : tryCloneSmallDelta M n = bytesCumAlloc M n := rfl

/-- Exact single-allocation `PhaseCreditSpec` for `cliConcat2Events bs0 bs1` via
`WirePksmTryFromHelpers.tryCloneSmallDelta` and `WireSignalHelpers.stepEvents_rustAlloc_pos`:
charges `tryCloneSmallDelta M n` (`≤ 122` B when `n > smallMaxReq M`) instead of `2 * n + 9539`. -/
theorem phaseCredit_cliConcat2Events_tryClone {M : AllocCostModel} [HasFineReallocCredit M]
    (bs0 bs1 : List (BitVec 8)) :
    PhaseCreditSpec M (· = cliConcat2Events bs0 bs1)
      (tryCloneSmallDelta M (bs0.length + bs1.length))
      (bytesLargeLive M (bs0.length + bs1.length))
      (bytesLargeLive M (bs0.length + bs1.length))
      (bs0.length + bs1.length) where
  req_align := by
    rintro _ rfl ev hev
    unfold cliConcat2Events at hev
    by_cases hz : bs0.length + bs1.length = 0
    · simp only [hz, ↓reduceIte] at hev
      nomatch hev
    · simp only [hz, ↓reduceIte] at hev
      exact req_align_of_rustAllocEvents (Nat.le_refl _) (by decide) ev hev
  credit_le := by
    rintro st0 _ rfl
    unfold cliConcat2Events
    by_cases hz : bs0.length + bs1.length = 0
    · simp only [hz, ↓reduceIte, AllocCostModel.stepEvents_nil,
        tryCloneSmallDelta, bytesLargeLive_zero, Nat.add_zero]
      exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_max_left _ _⟩
    · simp only [hz, ↓reduceIte, tryCloneSmallDelta_eq_bytesCumAlloc]
      exact stepEvents_rustAlloc_pos M (by decide) (Nat.pos_of_ne_zero hz) st0

theorem tryCloneSmallDelta_le_smallMaxAff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {n cap : Nat} (hle : n ≤ cap) :
    tryCloneSmallDelta M n ≤ 2 * min cap (HasFineReallocCredit.smallMaxReq M) + 9539 := by
  unfold tryCloneSmallDelta
  split
  · exact Nat.zero_le _
  · split
    · rename_i _ hsm
      have hmin : n ≤ min cap (HasFineReallocCredit.smallMaxReq M) := Nat.le_min.mpr ⟨hle, hsm⟩
      exact Nat.le_trans (hM.smallAlloc_le hsm)
        (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hmin) 9539)
    · exact Nat.le_trans hM.meta_le
        (Nat.le_trans (by decide : 122 ≤ 9539) (Nat.le_add_left 9539 _))

theorem tryCloneSmallDelta_le_tightCap {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hT : CliRunTightHyps M) {n cap : Nat} (hle : n ≤ cap) :
    tryCloneSmallDelta M n ≤ min (2 * cap + 9539) maxTryCloneSmallBytes := by
  refine Nat.le_min.mpr ⟨?_, ?_⟩
  · rw [tryCloneSmallDelta_eq_bytesCumAlloc]
    exact Nat.le_trans (bytesCumAlloc_le_aff hM n)
      (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hle) 9539)
  · unfold tryCloneSmallDelta
    split
    · exact Nat.zero_le _
    · split
      · rename_i _ hsm
        exact hT.hSmallAllocCap n hsm
      · exact Nat.le_trans hM.meta_le (by unfold maxTryCloneSmallBytes; decide)

def R2ConcatTailEnv (wireOutCap : Nat) (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨ ∃ (bs0 : List (BitVec 8)), bs0.length ≤ 1 ∧
    ∃ (bs1 : List (BitVec 8)), bs1.length ≤ wireOutCap ∧
      SeqEnv (· = cliConcat2Events bs0 bs1) FreeOnlyEvs evs

def R2Env (EncEnv : List AllocEvent → Prop) (wireOutCap : Nat) (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨ SeqEnv EncEnv (R2ConcatTailEnv wireOutCap) evs
def r2TailCum (M : AllocCostModel) [HasFineReallocCredit M] (wireOutCap : Nat) : Nat :=
  2 * min (1 + wireOutCap) (HasFineReallocCredit.smallMaxReq M) + 9539
def r2TailTightCum (wireOutCap : Nat) : Nat :=
  min (2 * (1 + wireOutCap) + 9539) maxTryCloneSmallBytes
def r2TailLive (M : AllocCostModel) [HasFineReallocCredit M] (wireOutCap : Nat) : Nat :=
  if 1 + wireOutCap ≤ HasFineReallocCredit.smallMaxReq M then 0 else (1 + wireOutCap) + 8195
def r2TailPeak (M : AllocCostModel) [HasFineReallocCredit M] (wireOutCap : Nat) : Nat :=
  r2TailLive M wireOutCap
def r2TailMaxReq (wireOutCap : Nat) : Nat := 1 + wireOutCap
def r2DeltaCum (M : AllocCostModel) [HasFineReallocCredit M] (c_e wireOutCap : Nat) : Nat :=
  c_e + r2TailCum M wireOutCap
def r2TightDeltaCum (c_e wireOutCap : Nat) : Nat := c_e + r2TailTightCum wireOutCap
def r2DeltaLive (M : AllocCostModel) [HasFineReallocCredit M] (l_e wireOutCap : Nat) : Nat :=
  l_e + r2TailLive M wireOutCap
def r2DeltaPeak (M : AllocCostModel) [HasFineReallocCredit M] (l_e p_e wireOutCap : Nat) : Nat :=
  max p_e (l_e + r2TailPeak M wireOutCap)
def r2MaxReq (r_e wireOutCap : Nat) : Nat := max r_e (r2TailMaxReq wireOutCap)

theorem r2TailCum_fine_1MiB : r2TailCum fineCostModel 1048576 = 279873 := by
  unfold r2TailCum; rw [fineCostModel_smallMaxReq_eq]; decide

theorem r2TailTightCum_1MiB : r2TailTightCum 1048576 = 143484 := by
  unfold r2TailTightCum maxTryCloneSmallBytes; decide

theorem bytesLargeLive_le_r2TailLive {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {n wireOutCap : Nat} (hle : n ≤ 1 + wireOutCap) :
    bytesLargeLive M n ≤ r2TailLive M wireOutCap := by
  unfold bytesLargeLive r2TailLive
  by_cases hcap : 1 + wireOutCap ≤ HasFineReallocCredit.smallMaxReq M
  · have hsm : n ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hle hcap
    simp only [hsm, hcap, ↓reduceIte]
    exact Nat.le_refl 0
  · simp only [hcap, ↓reduceIte]
    split
    · exact Nat.zero_le _
    · rename_i hnot
      exact Nat.le_trans (hM.largeCost_le (Nat.lt_of_not_ge hnot))
        (Nat.add_le_add_right hle 8195)

theorem r2ConcatTail_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (wireOutCap : Nat) :
    PhaseCreditSpec M (R2ConcatTailEnv wireOutCap)
      (r2TailCum M wireOutCap) (r2TailLive M wireOutCap)
      (r2TailPeak M wireOutCap) (r2TailMaxReq wireOutCap) :=
  phaseCredit_or_freeOnly_left hM (fun _ h => h)
    (phaseCredit_exists_guarded fun bs0 h0 => phaseCredit_exists_guarded fun bs1 h1 =>
      have hlen : bs0.length + bs1.length ≤ 1 + wireOutCap := Nat.add_le_add h0 h1
      have hlive : bytesLargeLive M (bs0.length + bs1.length) ≤ r2TailLive M wireOutCap :=
        bytesLargeLive_le_r2TailLive hM hlen
      phaseCredit_seq_freeOnly_right hM
        ((phaseCredit_cliConcat2Events_tryClone (M := M) bs0 bs1).mono
          (tryCloneSmallDelta_le_smallMaxAff hM hlen) hlive hlive hlen)
        (fun _ h => h) (Nat.le_refl _))

theorem r2ConcatTail_tight_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hT : CliRunTightHyps M) (wireOutCap : Nat) :
    PhaseCreditSpec M (R2ConcatTailEnv wireOutCap)
      (r2TailTightCum wireOutCap) (r2TailLive M wireOutCap)
      (r2TailPeak M wireOutCap) (r2TailMaxReq wireOutCap) :=
  phaseCredit_or_freeOnly_left hM (fun _ h => h)
    (phaseCredit_exists_guarded fun bs0 h0 => phaseCredit_exists_guarded fun bs1 h1 =>
      have hlen : bs0.length + bs1.length ≤ 1 + wireOutCap := Nat.add_le_add h0 h1
      have hlive : bytesLargeLive M (bs0.length + bs1.length) ≤ r2TailLive M wireOutCap :=
        bytesLargeLive_le_r2TailLive hM hlen
      phaseCredit_seq_freeOnly_right hM
        ((phaseCredit_cliConcat2Events_tryClone (M := M) bs0 bs1).mono
          (tryCloneSmallDelta_le_tightCap hM hT hlen) hlive hlive hlen)
        (fun _ h => h) (Nat.le_refl _))

theorem r2_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {EncEnv : List AllocEvent → Prop} {c_e l_e p_e r_e wireOutCap : Nat}
    (henc : PhaseCreditSpec M EncEnv c_e l_e p_e r_e) :
    PhaseCreditSpec M (R2Env EncEnv wireOutCap)
      (r2DeltaCum M c_e wireOutCap) (r2DeltaLive M l_e wireOutCap)
      (r2DeltaPeak M l_e p_e wireOutCap) (r2MaxReq r_e wireOutCap) :=
  phaseCredit_or_freeOnly_left hM (fun _ h => h) (henc.seq (r2ConcatTail_phaseCredit hM wireOutCap))

theorem r2_tight_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hT : CliRunTightHyps M) {EncEnv : List AllocEvent → Prop}
    {c_e l_e p_e r_e wireOutCap : Nat}
    (henc : PhaseCreditSpec M EncEnv c_e l_e p_e r_e) :
    PhaseCreditSpec M (R2Env EncEnv wireOutCap)
      (r2TightDeltaCum c_e wireOutCap) (r2DeltaLive M l_e wireOutCap)
      (r2DeltaPeak M l_e p_e wireOutCap) (r2MaxReq r_e wireOutCap) :=
  phaseCredit_or_freeOnly_left hM (fun _ h => h)
    (henc.seq (r2ConcatTail_tight_phaseCredit hM hT wireOutCap))

def SigTryFromSliceEnv (bs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  evs = [] ∨ SeqEnv (SigTryFromLoopBoundedEnv bs.length SigTryFromCaps.zero) (SigTryFromPostEnv bs) evs

theorem sigTryFromBoundedEnv_eq_sliceEnv (x : TryFromGhost) :
    SigTryFromBoundedEnv x = SigTryFromSliceEnv x.bytes := rfl

def R3aEnv (rest : List (BitVec 8)) (DecSigEnv : List AllocEvent → Prop)
    (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨ SeqEnv (SigTryFromSliceEnv rest)
    (fun evs2 => FreeOnlyEvs evs2 ∨ SeqEnv DecSigEnv FreeOnlyEvs evs2) evs

theorem r3a_phaseCredit_of_sig {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {rest : List (BitVec 8)} {DecSigEnv : List AllocEvent → Prop}
    {c_s l_s p_s r_s c_d l_d p_d r_d : Nat}
    (hsig : PhaseCreditSpec M (SigTryFromSliceEnv rest) c_s l_s p_s r_s)
    (hdec : PhaseCreditSpec M DecSigEnv c_d l_d p_d r_d) (hlp_d : l_d ≤ p_d) :
    PhaseCreditSpec M (R3aEnv rest DecSigEnv)
      (c_s + c_d) (l_s + l_d) (max p_s (l_s + p_d)) (max r_s r_d) :=
  phaseCredit_or_freeOnly_left hM (fun _ h => h)
    (hsig.seq (phaseCredit_or_freeOnly_left hM (fun _ h => h)
      (phaseCredit_seq_freeOnly_right hM hdec (fun _ h => h) hlp_d)))

def PksmTryFromSliceEnv (rest : List (BitVec 8)) : List AllocEvent → Prop :=
  PksmTryFromBoundedEnv ⟨0#64, rest, 0#64⟩

theorem pksmTryFromBoundedEnv_eq_sliceEnv (x : PksmGhost) :
    PksmTryFromBoundedEnv x = PksmTryFromSliceEnv x.bytes := rfl

def R3bEnv (PksmEnv DecPkEnv : List AllocEvent → Prop) (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨ SeqEnv PksmEnv (fun evs2 => FreeOnlyEvs evs2 ∨ SeqEnv DecPkEnv FreeOnlyEvs evs2) evs

theorem r3b_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {PksmEnv DecPkEnv : List AllocEvent → Prop}
    {c_k l_k p_k r_k c_d l_d p_d r_d : Nat}
    (hpksm : PhaseCreditSpec M PksmEnv c_k l_k p_k r_k)
    (hdec : PhaseCreditSpec M DecPkEnv c_d l_d p_d r_d) (hlp_d : l_d ≤ p_d) :
    PhaseCreditSpec M (R3bEnv PksmEnv DecPkEnv)
      (c_k + c_d) (l_k + l_d) (max p_k (l_k + p_d)) (max r_k r_d) :=
  phaseCredit_or_freeOnly_left hM (fun _ h => h)
    (hpksm.seq (phaseCredit_or_freeOnly_left hM (fun _ h => h)
      (phaseCredit_seq_freeOnly_right hM hdec (fun _ h => h) hlp_d)))

def RecvBadEnv (evs : List AllocEvent) : Prop := FreeOnlyEvs evs

theorem recvBad_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M) :
    PhaseCreditSpec M RecvBadEnv 0 0 0 0 := PhaseCreditSpec.freeOnly_of_hyps hM

def RecvArmEnv (stdin : List (BitVec 8)) (DecSigEnv : List AllocEvent → Prop)
    (PksmEnv : List (BitVec 8) → List AllocEvent → Prop)
    (DecPkEnv : List AllocEvent → Prop) (evs : List AllocEvent) : Prop :=
  match stdin with
  | b :: rest =>
    if b = 2#8 then R3aEnv rest DecSigEnv evs
    else if b = 3#8 then R3bEnv (PksmEnv rest) DecPkEnv evs
    else RecvBadEnv evs
  | [] => RecvBadEnv evs

def JoinEnv (evs : List AllocEvent) : Prop := FreeOnlyEvs evs

theorem join_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M) :
    PhaseCreditSpec M JoinEnv 0 0 0 0 := PhaseCreditSpec.freeOnly_of_hyps hM

/-! ## `RunArmEnv` and Top-Level `CliRunEnv` / `CliRunOpenedEnv` (`R0 → Arm → Join`) -/

structure CliRunCalleeEnvs where
  initEnv : List AllocEvent → Prop
  encEnv : List AllocEvent → Prop
  decSigEnv : List AllocEvent → Prop
  pksmEnv : List (BitVec 8) → List AllocEvent → Prop
  decPkEnv : List AllocEvent → Prop

structure CliRunSlotCalleeSpecs (M : AllocCostModel) [HasFineReallocCredit M]
    (E : CliRunCalleeEnvs) (stdinCap : Nat) where
  (initCum initLive initPeak initMaxReq : Nat)
  init_spec : PhaseCreditSpec M E.initEnv initCum initLive initPeak initMaxReq
  init_lp : initLive ≤ initPeak
  (encCum encLive encPeak encMaxReq : Nat)
  enc_spec : PhaseCreditSpec M E.encEnv encCum encLive encPeak encMaxReq
  enc_lp : encLive ≤ encPeak
  (decSigCum decSigLive decSigPeak decSigMaxReq : Nat)
  decSig_spec : PhaseCreditSpec M E.decSigEnv decSigCum decSigLive decSigPeak decSigMaxReq
  decSig_lp : decSigLive ≤ decSigPeak
  (pksmCum pksmLive pksmPeak pksmMaxReq : Nat)
  pksm_spec : ∀ rest, rest.length ≤ stdinCap →
    PhaseCreditSpec M (E.pksmEnv rest) pksmCum pksmLive pksmPeak pksmMaxReq
  pksm_lp : pksmLive ≤ pksmPeak
  (decPkCum decPkLive decPkPeak decPkMaxReq : Nat)
  decPk_spec : PhaseCreditSpec M E.decPkEnv decPkCum decPkLive decPkPeak decPkMaxReq
  decPk_lp : decPkLive ≤ decPkPeak

abbrev InitBundlePathsSpec (M : AllocCostModel) [HasFineReallocCredit M]
    (rd : ReadRule) (files : FsFiles) (c : CallV) (c_p l_p p_p r_p bundleCap : Nat) : Prop :=
  ∀ peer dir, c = .init peer dir →
    PhaseCreditSpec M (CliPathEnv dir (utf8 "identity-key")) c_p l_p p_p r_p ∧
    PhaseCreditSpec M (CliPathEnv dir (utf8 "registration-id")) c_p l_p p_p r_p ∧
    PhaseCreditSpec M (CliPathEnv dir (utf8 "signed-pre-key")) c_p l_p p_p r_p ∧
    PhaseCreditSpec M (CliPathEnv dir (utf8 "kyber-pre-key")) c_p l_p p_p r_p ∧
    PhaseCreditSpec M (CliPathEnv dir (utf8 "one-time-pre-key")) c_p l_p p_p r_p ∧
    (∀ name bs, rd files (pathOf dir name) = .ok bs → bs.length ≤ bundleCap)

def RunArmEnv (rd : ReadRule) (files : FsFiles) (E : CliRunCalleeEnvs)
    (wireOutCap : Nat) (stdin : List (BitVec 8)) (c : CallV) (evs : List AllocEvent) : Prop :=
  match c with
  | .keygen _ _ => FreeOnlyEvs evs
  | .init _ dir => InitArmEnv rd files dir E.initEnv evs
  | .send _ => R2Env E.encEnv wireOutCap evs
  | .recv _ => RecvArmEnv stdin E.decSigEnv E.pksmEnv E.decPkEnv evs

def CliRunOfR0Env (R0StageEnv : List AllocEvent → Prop) (rd : ReadRule)
    (E : CliRunCalleeEnvs) (wireOutCap : Nat) (g : RunCall) (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
  SeqEnv R0StageEnv (SeqEnv (RunArmEnv rd (runFiles g.i) E wireOutCap g.i.stdin g.c) JoinEnv) evs

abbrev CliRunEnv (uuidParse : UuidParser) (rd : ReadRule) (ownDir : DirGhost)
    (E : CliRunCalleeEnvs) (wireOutCap : Nat) (g : RunCall) (evs : List AllocEvent) : Prop :=
  CliRunOfR0Env (R0Env uuidParse rd (runFiles g.i) ownDir) rd E wireOutCap g evs

abbrev CliRunOpenedEnv (rd : ReadRule) (E : CliRunCalleeEnvs) (wireOutCap : Nat) (g : RunCall)
    (evs : List AllocEvent) : Prop :=
  CliRunOfR0Env (R0OpenedEnv rd (runFiles g.i)) rd E wireOutCap g evs

theorem initArmEnv_of_r1a {rd : ReadRule} {files : FsFiles} {dir : List (BitVec 8)}
    {InitEnv : List AllocEvent → Prop} {evs : List AllocEvent}
    (h1a : R1aEnv rd files dir evs) : InitArmEnv rd files dir InitEnv evs :=
  Or.inl h1a

theorem initArmEnv_of_r1a_r1b {rd : ReadRule} {files : FsFiles} {dir : List (BitVec 8)}
    {InitEnv : List AllocEvent → Prop} {evs₁ evs₂ : List AllocEvent}
    (h1a : R1aEnv rd files dir evs₁) (h1b : R1bEnv rd files dir evs₂) :
    InitArmEnv rd files dir InitEnv (evs₁ ++ evs₂) :=
  Or.inr ⟨evs₁, evs₂, rfl, h1a, Or.inr (Or.inl h1b)⟩

theorem initArmEnv_of_r1a_r1b_r1c {rd : ReadRule} {files : FsFiles} {dir : List (BitVec 8)}
    {InitEnv : List AllocEvent → Prop} {evs₁ evs₂ evs₃ : List AllocEvent}
    (h1a : R1aEnv rd files dir evs₁) (h1b : R1bEnv rd files dir evs₂)
    (h1c : R1cEnv InitEnv evs₃) :
    InitArmEnv rd files dir InitEnv (evs₁ ++ evs₂ ++ evs₃) :=
  Or.inr ⟨evs₁, evs₂ ++ evs₃, List.append_assoc evs₁ evs₂ evs₃, h1a,
    Or.inr (Or.inr ⟨evs₂, evs₃, rfl, h1b, Or.inr h1c⟩)⟩

theorem runArmEnv_nil (rd : ReadRule) (files : FsFiles) (E : CliRunCalleeEnvs)
    (wireOutCap : Nat) (stdin : List (BitVec 8)) (c : CallV) :
    RunArmEnv rd files E wireOutCap stdin c [] := by
  have hnil : FreeOnlyEvs [] := FreeOnlyAlign16Evs.nil.toFreeOnlyEvs
  cases c with
  | keygen _ _ => exact hnil
  | init _ _ => exact Or.inl (Or.inl hnil)
  | send _ => exact Or.inl hnil
  | recv _ =>
    unfold RunArmEnv RecvArmEnv
    rcases stdin with _ | ⟨b, rest⟩
    · exact hnil
    · by_cases hb2 : b = 2#8
      · simp only [hb2, ↓reduceIte]; exact Or.inl hnil
      · simp only [hb2, ↓reduceIte]
        by_cases hb3 : b = 3#8
        · simp only [hb3, ↓reduceIte]; exact Or.inl hnil
        · simp only [hb3, ↓reduceIte]; exact hnil

theorem cliRunOfR0Env_of_r0 {R0StageEnv : List AllocEvent → Prop} {rd : ReadRule}
    {E : CliRunCalleeEnvs} {wireOutCap : Nat} {g : RunCall} {evs : List AllocEvent}
    (h₀ : R0StageEnv evs) : CliRunOfR0Env R0StageEnv rd E wireOutCap g evs :=
  Or.inr (Or.inl h₀)

theorem cliRunOfR0Env_of_r0_arm {R0StageEnv : List AllocEvent → Prop} {rd : ReadRule}
    {E : CliRunCalleeEnvs} {wireOutCap : Nat} {g : RunCall} {evs₀ evs₁ : List AllocEvent}
    (h₀ : R0StageEnv evs₀)
    (h₁ : RunArmEnv rd (runFiles g.i) E wireOutCap g.i.stdin g.c evs₁) :
    CliRunOfR0Env R0StageEnv rd E wireOutCap g (evs₀ ++ evs₁) :=
  Or.inr (Or.inr ⟨evs₀, evs₁, rfl, h₀, Or.inl h₁⟩)

/-- Trailing `FreeOnlyEvs` closure of `CliRunOfR0Env`, discharging `JPlacedBudget.runPostPlaced_of_joinPost`
across both early-reject (`R0`) and arm-exit (`R0 ++ Arm`) continuations. -/
theorem cliRunOfR0Env_append_freeOnly {R0StageEnv : List AllocEvent → Prop} {rd : ReadRule}
    {E : CliRunCalleeEnvs} {wireOutCap : Nat} {g : RunCall} {evs₁ evs₂ : List AllocEvent}
    (h₁ : CliRunOfR0Env R0StageEnv rd E wireOutCap g evs₁) (h₂ : FreeOnlyEvs evs₂) :
    CliRunOfR0Env R0StageEnv rd E wireOutCap g (evs₁ ++ evs₂) := by
  rcases h₁ with hf₁ | hr0 | ⟨e₀, e_aj, rfl, he₀, haj⟩
  · exact Or.inl (freeOnlyEvs_append hf₁ h₂)
  · exact Or.inr (Or.inr ⟨evs₁, evs₂, rfl, hr0,
      Or.inr ⟨[], evs₂, rfl, runArmEnv_nil rd (runFiles g.i) E wireOutCap g.i.stdin g.c, h₂⟩⟩)
  · refine Or.inr (Or.inr ⟨e₀, e_aj ++ evs₂, List.append_assoc e₀ e_aj evs₂, he₀, ?_⟩)
    rcases haj with harm | ⟨e_a, e_j, rfl, harm, hj⟩
    · exact Or.inr ⟨e_aj, evs₂, rfl, harm, h₂⟩
    · exact Or.inr ⟨e_a, e_j ++ evs₂, List.append_assoc e_a e_j evs₂, harm,
        freeOnlyEvs_append hj h₂⟩

def sigSliceCum (stdinCap : Nat) : Nat := sigTryFromCapDeltaCum stdinCap
def sigSliceLive (stdinCap : Nat) : Nat := sigTryFromCapDeltaLive stdinCap
def sigSlicePeak (stdinCap : Nat) : Nat := sigTryFromCapDeltaPeak stdinCap
def sigSliceMaxReq (stdinCap : Nat) : Nat := sigTryFromCapMaxReq stdinCap

def pksmSliceCum (stdinCap : Nat) : Nat := pksmTryFromCapDeltaCum stdinCap
def pksmSliceLive (stdinCap : Nat) : Nat := pksmTryFromCapDeltaLive stdinCap
def pksmSlicePeak (stdinCap : Nat) : Nat := pksmTryFromCapDeltaPeak stdinCap
def pksmSliceMaxReq (stdinCap : Nat) : Nat := pksmTryFromCapMaxReq stdinCap

theorem pksmSliceLive_le_peak (stdinCap : Nat) : pksmSliceLive stdinCap ≤ pksmSlicePeak stdinCap := by
  unfold pksmSliceLive pksmSlicePeak pksmTryFromCapDeltaLive pksmTryFromCapDeltaPeak
    LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.pksmTryFromCapDeltaLive
    LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.pksmTryFromCapDeltaPeak
  exact Nat.le_add_right _ _

def recvArmDeltaCum {M : AllocCostModel} [HasFineReallocCredit M] {E : CliRunCalleeEnvs}
    {stdinCap : Nat} (S : CliRunSlotCalleeSpecs M E stdinCap) (c_sig : Nat) : Nat :=
  max (c_sig + S.decSigCum) (S.pksmCum + S.decPkCum)
def recvArmDeltaLive {M : AllocCostModel} [HasFineReallocCredit M] {E : CliRunCalleeEnvs}
    {stdinCap : Nat} (S : CliRunSlotCalleeSpecs M E stdinCap) (l_sig : Nat) : Nat :=
  max (l_sig + S.decSigLive) (S.pksmLive + S.decPkLive)
def recvArmDeltaPeak {M : AllocCostModel} [HasFineReallocCredit M] {E : CliRunCalleeEnvs}
    {stdinCap : Nat} (S : CliRunSlotCalleeSpecs M E stdinCap) (l_sig p_sig : Nat) : Nat :=
  max (max p_sig (l_sig + S.decSigPeak)) (max S.pksmPeak (S.pksmLive + S.decPkPeak))
def recvArmMaxReq {M : AllocCostModel} [HasFineReallocCredit M] {E : CliRunCalleeEnvs}
    {stdinCap : Nat} (S : CliRunSlotCalleeSpecs M E stdinCap) (r_sig : Nat) : Nat :=
  max (max r_sig S.decSigMaxReq) (max S.pksmMaxReq S.decPkMaxReq)

def runArmDeltaCum {M : AllocCostModel} [HasFineReallocCredit M] {E : CliRunCalleeEnvs}
    {stdinCap : Nat} (S : CliRunSlotCalleeSpecs M E stdinCap)
    (c_p bundleCap wireOutCap c_sig : Nat) : Nat :=
  max (initArmDeltaCum c_p bundleCap S.initCum)
    (max (r2DeltaCum M S.encCum wireOutCap) (recvArmDeltaCum S c_sig))
def runArmTightDeltaCum {M : AllocCostModel} [HasFineReallocCredit M] {E : CliRunCalleeEnvs}
    {stdinCap : Nat} (S : CliRunSlotCalleeSpecs M E stdinCap)
    (c_p bundleCap wireOutCap c_sig : Nat) : Nat :=
  max (initArmDeltaCum c_p bundleCap S.initCum)
    (max (r2TightDeltaCum S.encCum wireOutCap) (recvArmDeltaCum S c_sig))
def runArmDeltaLive {M : AllocCostModel} [HasFineReallocCredit M] {E : CliRunCalleeEnvs}
    {stdinCap : Nat} (S : CliRunSlotCalleeSpecs M E stdinCap) (l_p wireOutCap l_sig : Nat) : Nat :=
  max (initArmDeltaLive l_p S.initLive)
    (max (r2DeltaLive M S.encLive wireOutCap) (recvArmDeltaLive S l_sig))
def runArmDeltaPeak {M : AllocCostModel} [HasFineReallocCredit M] {E : CliRunCalleeEnvs}
    {stdinCap : Nat} (S : CliRunSlotCalleeSpecs M E stdinCap)
    (l_p p_p bundleCap wireOutCap l_sig p_sig : Nat) : Nat :=
  max (initArmDeltaPeak l_p p_p bundleCap S.initPeak)
    (max (r2DeltaPeak M S.encLive S.encPeak wireOutCap) (recvArmDeltaPeak S l_sig p_sig))
def runArmMaxReq {M : AllocCostModel} [HasFineReallocCredit M] {E : CliRunCalleeEnvs}
    {stdinCap : Nat} (S : CliRunSlotCalleeSpecs M E stdinCap)
    (r_p bundleCap wireOutCap r_sig : Nat) : Nat :=
  max (initArmMaxReq r_p bundleCap S.initMaxReq)
    (max (r2MaxReq S.encMaxReq wireOutCap) (recvArmMaxReq S r_sig))

theorem runArmDeltaLive_le_peak {M : AllocCostModel} [HasFineReallocCredit M]
    {E : CliRunCalleeEnvs} {stdinCap : Nat} (S : CliRunSlotCalleeSpecs M E stdinCap)
    {l_p p_p bundleCap wireOutCap l_sig p_sig : Nat} :
    runArmDeltaLive S l_p wireOutCap l_sig ≤
      runArmDeltaPeak S l_p p_p bundleCap wireOutCap l_sig p_sig := by
  have hinit : initArmDeltaLive l_p S.initLive ≤ initArmDeltaPeak l_p p_p bundleCap S.initPeak :=
    Nat.le_trans (Nat.add_le_add_left
      (Nat.le_trans (Nat.add_le_add_left S.init_lp _) (Nat.le_max_right _ _)) _) (Nat.le_max_right _ _)
  have hr2 : r2DeltaLive M S.encLive wireOutCap ≤ r2DeltaPeak M S.encLive S.encPeak wireOutCap :=
    Nat.le_max_right _ _
  have hrecv : recvArmDeltaLive S l_sig ≤ recvArmDeltaPeak S l_sig p_sig :=
    max_le_max (Nat.le_trans (Nat.add_le_add_left S.decSig_lp _) (Nat.le_max_right _ _))
      (Nat.le_trans (Nat.add_le_add_left S.decPk_lp _) (Nat.le_max_right _ _))
  exact max3_mono hinit hr2 hrecv

private theorem runArmOfR2_phaseCredit_of_callees {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {rd : ReadRule} {files : FsFiles} {E : CliRunCalleeEnvs}
    {stdinCap c_p l_p p_p r_p bundleCap c_r2 c_sig l_sig p_sig r_sig : Nat}
    (S : CliRunSlotCalleeSpecs M E stdinCap) (wireOutCap : Nat)
    (hr2 : PhaseCreditSpec M (R2Env E.encEnv wireOutCap) c_r2
      (r2DeltaLive M S.encLive wireOutCap) (r2DeltaPeak M S.encLive S.encPeak wireOutCap)
      (r2MaxReq S.encMaxReq wireOutCap))
    {stdin : List (BitVec 8)} {c : CallV} (hstdin : stdin.length ≤ stdinCap)
    (hpaths : InitBundlePathsSpec M rd files c c_p l_p p_p r_p bundleCap)
    (hsig : ∀ rest, rest.length ≤ stdinCap →
      PhaseCreditSpec M (SigTryFromSliceEnv rest) c_sig l_sig p_sig r_sig) :
    PhaseCreditSpec M (RunArmEnv rd files E wireOutCap stdin c)
      (max (initArmDeltaCum c_p bundleCap S.initCum) (max c_r2 (recvArmDeltaCum S c_sig)))
      (runArmDeltaLive S l_p wireOutCap l_sig)
      (runArmDeltaPeak S l_p p_p bundleCap wireOutCap l_sig p_sig)
      (runArmMaxReq S r_p bundleCap wireOutCap r_sig) := by
  cases c with
  | keygen _ _ =>
    exact (PhaseCreditSpec.freeOnly_of_hyps hM).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  | init peer dir =>
    obtain ⟨hpIk, hpReg, hpSpk, hpKpk, hpOpk, hcap⟩ := hpaths peer dir rfl
    exact (initArm_phaseCredit_of_paths hM hpIk hpReg hpSpk hpKpk hpOpk hcap
      S.init_spec S.init_lp).mono
      (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  | send _ =>
    exact hr2.mono
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
  | recv _ =>
    have hrecv : PhaseCreditSpec M (RecvArmEnv stdin E.decSigEnv E.pksmEnv E.decPkEnv)
        (recvArmDeltaCum S c_sig) (recvArmDeltaLive S l_sig)
        (recvArmDeltaPeak S l_sig p_sig) (recvArmMaxReq S r_sig) := by
      unfold RecvArmEnv; rcases stdin with _ | ⟨b, rest⟩
      · exact (recvBad_phaseCredit hM).mono
          (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
      · have hrest : rest.length ≤ stdinCap := Nat.le_of_succ_le hstdin
        by_cases hb2 : b = 2#8
        · simp only [hb2, ↓reduceIte]
          exact (r3a_phaseCredit_of_sig hM (hsig rest hrest) S.decSig_spec S.decSig_lp).mono
            (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _)
        · simp only [hb2, ↓reduceIte]
          by_cases hb3 : b = 3#8
          · simp only [hb3, ↓reduceIte]
            exact (r3b_phaseCredit hM (S.pksm_spec rest hrest) S.decPk_spec S.decPk_lp).mono
              (Nat.le_max_right _ _) (Nat.le_max_right _ _)
              (Nat.le_max_right _ _) (Nat.le_max_right _ _)
          · simp only [hb3, ↓reduceIte]
            exact (recvBad_phaseCredit hM).mono
              (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    exact hrecv.mono
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))

theorem runArm_phaseCredit_of_callees {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {rd : ReadRule} {files : FsFiles} {E : CliRunCalleeEnvs}
    {stdinCap c_p l_p p_p r_p bundleCap c_sig l_sig p_sig r_sig : Nat}
    (S : CliRunSlotCalleeSpecs M E stdinCap) (wireOutCap : Nat)
    {stdin : List (BitVec 8)} {c : CallV} (hstdin : stdin.length ≤ stdinCap)
    (hpaths : InitBundlePathsSpec M rd files c c_p l_p p_p r_p bundleCap)
    (hsig : ∀ rest, rest.length ≤ stdinCap →
      PhaseCreditSpec M (SigTryFromSliceEnv rest) c_sig l_sig p_sig r_sig) :
    PhaseCreditSpec M (RunArmEnv rd files E wireOutCap stdin c)
      (runArmDeltaCum S c_p bundleCap wireOutCap c_sig) (runArmDeltaLive S l_p wireOutCap l_sig)
      (runArmDeltaPeak S l_p p_p bundleCap wireOutCap l_sig p_sig)
      (runArmMaxReq S r_p bundleCap wireOutCap r_sig) :=
  runArmOfR2_phaseCredit_of_callees hM S wireOutCap (r2_phaseCredit hM S.enc_spec)
    hstdin hpaths hsig

theorem runArm_tight_phaseCredit_of_callees {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hT : CliRunTightHyps M) {rd : ReadRule} {files : FsFiles}
    {E : CliRunCalleeEnvs} {stdinCap c_p l_p p_p r_p bundleCap c_sig l_sig p_sig r_sig : Nat}
    (S : CliRunSlotCalleeSpecs M E stdinCap) (wireOutCap : Nat)
    {stdin : List (BitVec 8)} {c : CallV} (hstdin : stdin.length ≤ stdinCap)
    (hpaths : InitBundlePathsSpec M rd files c c_p l_p p_p r_p bundleCap)
    (hsig : ∀ rest, rest.length ≤ stdinCap →
      PhaseCreditSpec M (SigTryFromSliceEnv rest) c_sig l_sig p_sig r_sig) :
    PhaseCreditSpec M (RunArmEnv rd files E wireOutCap stdin c)
      (runArmTightDeltaCum S c_p bundleCap wireOutCap c_sig) (runArmDeltaLive S l_p wireOutCap l_sig)
      (runArmDeltaPeak S l_p p_p bundleCap wireOutCap l_sig p_sig)
      (runArmMaxReq S r_p bundleCap wireOutCap r_sig) :=
  runArmOfR2_phaseCredit_of_callees hM S wireOutCap (r2_tight_phaseCredit hM hT S.enc_spec)
    hstdin hpaths hsig

theorem cliRunOfR0_phaseCredit_of_callees {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {R0StageEnv : List AllocEvent → Prop} {rd : ReadRule}
    {E : CliRunCalleeEnvs} {g : RunCall}
    {stdinCap c₀ l₀ p₀ r₀ c_p l_p p_p r_p bundleCap c_sig l_sig p_sig r_sig : Nat}
    (S : CliRunSlotCalleeSpecs M E stdinCap) (wireOutCap : Nat)
    (hR0 : PhaseCreditSpec M R0StageEnv c₀ l₀ p₀ r₀) (hstdin : g.i.stdin.length ≤ stdinCap)
    (hpaths : InitBundlePathsSpec M rd (runFiles g.i) g.c c_p l_p p_p r_p bundleCap)
    (hsig : ∀ rest, rest.length ≤ stdinCap →
      PhaseCreditSpec M (SigTryFromSliceEnv rest) c_sig l_sig p_sig r_sig) :
    PhaseCreditSpec M (CliRunOfR0Env R0StageEnv rd E wireOutCap g)
      (c₀ + runArmDeltaCum S c_p bundleCap wireOutCap c_sig)
      (l₀ + runArmDeltaLive S l_p wireOutCap l_sig)
      (max p₀ (l₀ + runArmDeltaPeak S l_p p_p bundleCap wireOutCap l_sig p_sig))
      (max r₀ (runArmMaxReq S r_p bundleCap wireOutCap r_sig)) :=
  phaseCredit_or_freeOnly_left hM (fun _ h => h)
    (phaseCredit_runDispatch hM hR0
      (runArm_phaseCredit_of_callees hM S wireOutCap hstdin hpaths hsig)
      (fun _ h => h) (runArmDeltaLive_le_peak S))

theorem cliRunOfR0_tight_phaseCredit_of_callees {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hT : CliRunTightHyps M) {R0StageEnv : List AllocEvent → Prop}
    {rd : ReadRule} {E : CliRunCalleeEnvs} {g : RunCall}
    {stdinCap c₀ l₀ p₀ r₀ c_p l_p p_p r_p bundleCap c_sig l_sig p_sig r_sig : Nat}
    (S : CliRunSlotCalleeSpecs M E stdinCap) (wireOutCap : Nat)
    (hR0 : PhaseCreditSpec M R0StageEnv c₀ l₀ p₀ r₀) (hstdin : g.i.stdin.length ≤ stdinCap)
    (hpaths : InitBundlePathsSpec M rd (runFiles g.i) g.c c_p l_p p_p r_p bundleCap)
    (hsig : ∀ rest, rest.length ≤ stdinCap →
      PhaseCreditSpec M (SigTryFromSliceEnv rest) c_sig l_sig p_sig r_sig) :
    PhaseCreditSpec M (CliRunOfR0Env R0StageEnv rd E wireOutCap g)
      (c₀ + runArmTightDeltaCum S c_p bundleCap wireOutCap c_sig)
      (l₀ + runArmDeltaLive S l_p wireOutCap l_sig)
      (max p₀ (l₀ + runArmDeltaPeak S l_p p_p bundleCap wireOutCap l_sig p_sig))
      (max r₀ (runArmMaxReq S r_p bundleCap wireOutCap r_sig)) :=
  phaseCredit_or_freeOnly_left hM (fun _ h => h)
    (phaseCredit_runDispatch hM hR0
      (runArm_tight_phaseCredit_of_callees hM hT S wireOutCap hstdin hpaths hsig)
      (fun _ h => h) (runArmDeltaLive_le_peak S))

theorem cliRun_phaseCredit_of_callees {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {rd : ReadRule} {ownDir : DirGhost} {E : CliRunCalleeEnvs} {g : RunCall}
    {stdinCap c_g l_g p_g r_g c_p l_p p_p r_p bundleCap c_sig l_sig p_sig r_sig : Nat}
    (S : CliRunSlotCalleeSpecs M E stdinCap) (wireOutCap : Nat)
    (hget : PhaseCreditSpec M
      (CliDirGetEnv (ReadFileRuleEnv rd) (runFiles g.i) ownDir (utf8 "address")) c_g l_g p_g r_g)
    (hstdin : g.i.stdin.length ≤ stdinCap)
    (hpaths : InitBundlePathsSpec M rd (runFiles g.i) g.c c_p l_p p_p r_p bundleCap)
    (hsig : ∀ rest, rest.length ≤ stdinCap →
      PhaseCreditSpec M (SigTryFromSliceEnv rest) c_sig l_sig p_sig r_sig) :
    PhaseCreditSpec M (CliRunEnv uuidTryParse rd ownDir E wireOutCap g)
      ((c_g + addressTryParseDeltaCum) + runArmDeltaCum S c_p bundleCap wireOutCap c_sig)
      ((l_g + addressTryParseDeltaLive) + runArmDeltaLive S l_p wireOutCap l_sig)
      (max (max p_g (l_g + addressTryParseDeltaPeak))
        ((l_g + addressTryParseDeltaLive) +
          runArmDeltaPeak S l_p p_p bundleCap wireOutCap l_sig p_sig))
      (max (max r_g addressTryParseMaxReq) (runArmMaxReq S r_p bundleCap wireOutCap r_sig)) :=
  cliRunOfR0_phaseCredit_of_callees hM S wireOutCap
    (r0_tryParse_phaseCredit_of_dirGet hM hget) hstdin hpaths hsig

theorem cliRunOpened_phaseCredit_of_callees {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {rd : ReadRule} {E : CliRunCalleeEnvs} {g : RunCall}
    {stdinCap c_p0 l_p0 p_p0 r_p0 ownFileCap c_p l_p p_p r_p bundleCap
     c_sig l_sig p_sig r_sig : Nat}
    (S : CliRunSlotCalleeSpecs M E stdinCap) (wireOutCap : Nat)
    (hpathOwn : PhaseCreditSpec M
      (CliPathEnv StoresGhost.opened.identity.own.path (utf8 "address")) c_p0 l_p0 p_p0 r_p0)
    (hownCap : ∀ bs,
      rd (runFiles g.i) (pathOf StoresGhost.opened.identity.own.path (utf8 "address")) = .ok bs →
      bs.length ≤ ownFileCap)
    (hstdin : g.i.stdin.length ≤ stdinCap)
    (hpaths : InitBundlePathsSpec M rd (runFiles g.i) g.c c_p l_p p_p r_p bundleCap)
    (hsig : ∀ rest, rest.length ≤ stdinCap →
      PhaseCreditSpec M (SigTryFromSliceEnv rest) c_sig l_sig p_sig r_sig) :
    PhaseCreditSpec M (CliRunOpenedEnv rd E wireOutCap g)
      ((c_p0 + tempFilePostCum ownFileCap addressTryParseDeltaCum) +
        runArmDeltaCum S c_p bundleCap wireOutCap c_sig)
      ((l_p0 + tempFilePostLive addressTryParseDeltaLive) +
        runArmDeltaLive S l_p wireOutCap l_sig)
      (max (max p_p0 (l_p0 + tempFilePostPeak ownFileCap addressTryParseDeltaPeak))
        ((l_p0 + tempFilePostLive addressTryParseDeltaLive) +
          runArmDeltaPeak S l_p p_p bundleCap wireOutCap l_sig p_sig))
      (max (max r_p0 (tempFilePostMaxReq ownFileCap addressTryParseMaxReq))
        (runArmMaxReq S r_p bundleCap wireOutCap r_sig)) :=
  cliRunOfR0_phaseCredit_of_callees hM S wireOutCap
    (r0Opened_phaseCredit_of_path hM hpathOwn hownCap) hstdin hpaths hsig

/-! ## Instantiations with `DirPeakSpec`, `WireMsgPeakSpec`, and `WirePksmTryFromPeakSpec` -/

theorem sigTryFromSlice_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : WireLowInterceptHyps M)
    {rest : List (BitVec 8)} {stdinCap : Nat} (hlen : rest.length ≤ stdinCap) :
    PhaseCreditSpec M (SigTryFromSliceEnv rest)
      (sigSliceCum stdinCap) (sigSliceLive stdinCap)
      (sigSlicePeak stdinCap) (sigSliceMaxReq stdinCap) := by
  let x : TryFromGhost := ⟨0#64, rest, 0#64⟩
  have h := sigTryFrom_phaseCredit hM hLow x
  rw [sigTryFromBoundedEnv_eq_sliceEnv x] at h
  exact h.mono
    (sigTryFromDeltaCum_le_cap hlen)
    (sigTryFromDeltaLive_le_cap hlen)
    (sigTryFromDeltaPeak_le_cap hlen)
    (sigTryFromMaxReq_le_cap hlen)

theorem r3a_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : WireLowInterceptHyps M)
    {rest : List (BitVec 8)} {DecSigEnv : List AllocEvent → Prop}
    {stdinCap c_d l_d p_d r_d : Nat} (hrest : rest.length ≤ stdinCap)
    (hdec : PhaseCreditSpec M DecSigEnv c_d l_d p_d r_d) (hlp_d : l_d ≤ p_d) :
    PhaseCreditSpec M (R3aEnv rest DecSigEnv)
      (sigSliceCum stdinCap + c_d) (sigSliceLive stdinCap + l_d)
      (max (sigSlicePeak stdinCap) (sigSliceLive stdinCap + p_d))
      (max (sigSliceMaxReq stdinCap) r_d) :=
  r3a_phaseCredit_of_sig hM (sigTryFromSlice_phaseCredit hM hLow hrest) hdec hlp_d

theorem pksmTryFromSlice_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : WireLowInterceptHyps M)
    {rest : List (BitVec 8)} {stdinCap : Nat} (hlen : rest.length ≤ stdinCap) :
    PhaseCreditSpec M (PksmTryFromSliceEnv rest)
      (pksmSliceCum stdinCap) (pksmSliceLive stdinCap)
      (pksmSlicePeak stdinCap) (pksmSliceMaxReq stdinCap) :=
  (pksmTryFrom_phaseCredit hM hLow ⟨0#64, rest, 0#64⟩).mono
    (pksmTryFromDeltaCum_le_cap hlen)
    (pksmTryFromDeltaLive_le_cap hlen)
    (pksmTryFromDeltaPeak_le_cap hlen)
    (pksmTryFromMaxReq_le_cap hlen)

theorem r3b_slice_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : WireLowInterceptHyps M)
    {rest : List (BitVec 8)} {DecPkEnv : List AllocEvent → Prop}
    {stdinCap c_d l_d p_d r_d : Nat} (hrest : rest.length ≤ stdinCap)
    (hdec : PhaseCreditSpec M DecPkEnv c_d l_d p_d r_d) (hlp_d : l_d ≤ p_d) :
    PhaseCreditSpec M (R3bEnv (PksmTryFromSliceEnv rest) DecPkEnv)
      (pksmSliceCum stdinCap + c_d) (pksmSliceLive stdinCap + l_d)
      (max (pksmSlicePeak stdinCap) (pksmSliceLive stdinCap + p_d))
      (max (pksmSliceMaxReq stdinCap) r_d) :=
  r3b_phaseCredit hM (pksmTryFromSlice_phaseCredit hM hLow hrest) hdec hlp_d

theorem r0_general_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (uuidParse : UuidParser) (rd : ReadRule) (files : FsFiles)
    (ownDir : DirGhost) {maxDir maxEntries maxVal fileCap : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal ownDir)
    (hcap : ∀ bs, rd files (pathOf ownDir.path (utf8 "address")) = .ok bs → bs.length ≤ fileCap) :
    let ownCap := max maxVal fileCap
    let c_g := dirGetRuleDeltaCum maxDir 7 maxVal fileCap
    let l_g := dirGetRuleDeltaLive maxDir 7 maxVal fileCap
    let p_g := dirGetRuleDeltaPeak maxDir 7 maxVal fileCap
    let r_g := dirGetRuleMaxReq maxDir 7 maxVal fileCap
    PhaseCreditSpec M (R0Env uuidParse rd files ownDir)
      (c_g + (2 * ownCap + 9539)) (l_g + (ownCap + 8195))
      (max p_g (l_g + (ownCap + 8195))) (max r_g ownCap) := by
  intro ownCap c_g l_g p_g r_g
  have hget := dirGet_rule_phaseCredit hM rd files ownDir (utf8 "address")
    hdc utf8_address_length_le hcap
  have hown_le : ∀ ownB, ownDir.get rd files (utf8 "address") = .ok ownB → ownB.length ≤ ownCap := by
    intro ownB hok; unfold DirGhost.get at hok
    cases hfind : ownDir.changed.find? (fun kv => kv.1 == utf8 "address") with
    | some kv =>
      rw [hfind] at hok; injection hok with hv; subst hv
      exact Nat.le_trans (hdc.changed_val_le kv.1 kv.2 (List.mem_of_find?_eq_some hfind))
        (Nat.le_max_left _ _)
    | none => rw [hfind] at hok; exact Nat.le_trans (hcap ownB hok) (Nat.le_max_right _ _)
  have hpost : PhaseCreditSpec M
      (match ownDir.get rd files (utf8 "address") with
       | .error () => FreeOnlyEvs | .ok ownB => R0PostGetEnv uuidParse ownB)
      (2 * ownCap + 9539) (ownCap + 8195) (ownCap + 8195) ownCap := by
    cases hgo : ownDir.get rd files (utf8 "address") with
    | error _ =>
      exact (PhaseCreditSpec.freeOnly_of_hyps hM).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    | ok ownB =>
      have hlen := hown_le ownB hgo
      have ha : PhaseCreditSpec M (· = addressEvents uuidParse ownB)
          (2 * ownCap + 9539) (ownCap + 8195) (ownCap + 8195) ownCap :=
        (addressEvents_phaseCredit hM uuidParse ownB).mono
          (by omega) (by omega) (by omega) hlen
      exact phaseCredit_or_freeOnly_left hM (fun _ h => h)
        (phaseCredit_seq_freeOnly_right hM ha
          (freeOnlyEvs_seq_deallocBytes1OfLen ownB.length) (Nat.le_refl _))
  exact phaseCredit_or_freeOnly_left hM (fun _ h => h) (hget.seq hpost)

theorem initBundlePaths_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {rd : ReadRule} {files : FsFiles} {c : CallV} {maxInitDir bundleCap : Nat}
    (hinitDir : ∀ peer dir, c = .init peer dir → dir.length ≤ maxInitDir ∧
      (∀ name bs, rd files (pathOf dir name) = .ok bs → bs.length ≤ bundleCap)) :
    InitBundlePathsSpec M rd files c
      (pathDeltaCum maxInitDir 16) (pathDeltaLive maxInitDir 16)
      (pathDeltaPeak maxInitDir 16) (pathMaxReq maxInitDir 16) bundleCap := by
  obtain ⟨hnIk, hnReg, hnSpk, hnKpk, hnOpk⟩ := utf8_bundleNames_length_le_16
  intro peer dir hc; obtain ⟨hd, hbc⟩ := hinitDir peer dir hc
  exact ⟨path_phaseCredit hM hd hnIk, path_phaseCredit hM hd hnReg,
    path_phaseCredit hM hd hnSpk, path_phaseCredit hM hd hnKpk,
    path_phaseCredit hM hd hnOpk, hbc⟩

def cliRunDeltaCum {M : AllocCostModel} [HasFineReallocCredit M] {E : CliRunCalleeEnvs}
    {stdinCap : Nat} (S : CliRunSlotCalleeSpecs M E stdinCap)
    (maxInitDir fileCap bundleCap wireOutCap : Nat) : Nat :=
  (dirGetRuleDeltaCum 26 7 0 fileCap + addressTryParseDeltaCum) +
    runArmDeltaCum S (pathDeltaCum maxInitDir 16) bundleCap wireOutCap (sigSliceCum stdinCap)
def cliRunDeltaLive {M : AllocCostModel} [HasFineReallocCredit M] {E : CliRunCalleeEnvs}
    {stdinCap : Nat} (S : CliRunSlotCalleeSpecs M E stdinCap)
    (maxInitDir fileCap wireOutCap : Nat) : Nat :=
  (dirGetRuleDeltaLive 26 7 0 fileCap + addressTryParseDeltaLive) +
    runArmDeltaLive S (pathDeltaLive maxInitDir 16) wireOutCap (sigSliceLive stdinCap)
def cliRunDeltaPeak {M : AllocCostModel} [HasFineReallocCredit M] {E : CliRunCalleeEnvs}
    {stdinCap : Nat} (S : CliRunSlotCalleeSpecs M E stdinCap)
    (maxInitDir fileCap bundleCap wireOutCap : Nat) : Nat :=
  let l_g := dirGetRuleDeltaLive 26 7 0 fileCap
  max (max (dirGetRuleDeltaPeak 26 7 0 fileCap) (l_g + addressTryParseDeltaPeak))
    ((l_g + addressTryParseDeltaLive) +
      runArmDeltaPeak S (pathDeltaLive maxInitDir 16) (pathDeltaPeak maxInitDir 16)
        bundleCap wireOutCap (sigSliceLive stdinCap) (sigSlicePeak stdinCap))
def cliRunMaxReq {M : AllocCostModel} [HasFineReallocCredit M] {E : CliRunCalleeEnvs}
    {stdinCap : Nat} (S : CliRunSlotCalleeSpecs M E stdinCap)
    (maxInitDir fileCap bundleCap wireOutCap : Nat) : Nat :=
  max (max (dirGetRuleMaxReq 26 7 0 fileCap) addressTryParseMaxReq)
    (runArmMaxReq S (pathMaxReq maxInitDir 16) bundleCap wireOutCap (sigSliceMaxReq stdinCap))

theorem cliRun_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : WireLowInterceptHyps M)
    {rd : ReadRule} {E : CliRunCalleeEnvs} {g : RunCall}
    {stdinCap maxInitDir fileCap bundleCap : Nat}
    (S : CliRunSlotCalleeSpecs M E stdinCap) (wireOutCap : Nat)
    (hstdin : g.i.stdin.length ≤ stdinCap)
    (hownCap : ∀ bs,
      rd (runFiles g.i) (pathOf StoresGhost.opened.identity.own.path (utf8 "address")) = .ok bs →
      bs.length ≤ fileCap)
    (hinitDir : ∀ peer dir, g.c = .init peer dir → dir.length ≤ maxInitDir ∧
      (∀ name bs, rd (runFiles g.i) (pathOf dir name) = .ok bs → bs.length ≤ bundleCap)) :
    PhaseCreditSpec M (CliRunEnv uuidTryParse rd StoresGhost.opened.identity.own E wireOutCap g)
      (cliRunDeltaCum S maxInitDir fileCap bundleCap wireOutCap)
      (cliRunDeltaLive S maxInitDir fileCap wireOutCap)
      (cliRunDeltaPeak S maxInitDir fileCap bundleCap wireOutCap)
      (cliRunMaxReq S maxInitDir fileCap bundleCap wireOutCap) :=
  cliRun_phaseCredit_of_callees hM S wireOutCap
    (dirGet_rule_phaseCredit hM rd (runFiles g.i) StoresGhost.opened.identity.own
      (utf8 "address") dirDomainCaps_opened_own utf8_address_length_le hownCap)
    hstdin (initBundlePaths_phaseCredit hM hinitDir)
    (fun _ hrest => sigTryFromSlice_phaseCredit hM hLow hrest)

def cliRunOpenedDeltaCum {M : AllocCostModel} [HasFineReallocCredit M] {E : CliRunCalleeEnvs}
    {stdinCap : Nat} (S : CliRunSlotCalleeSpecs M E stdinCap)
    (maxInitDir fileCap bundleCap wireOutCap : Nat) : Nat :=
  (pathDeltaCum 26 7 + tempFilePostCum fileCap addressTryParseDeltaCum) +
    runArmDeltaCum S (pathDeltaCum maxInitDir 16) bundleCap wireOutCap (sigSliceCum stdinCap)
def cliRunOpenedDeltaLive {M : AllocCostModel} [HasFineReallocCredit M] {E : CliRunCalleeEnvs}
    {stdinCap : Nat} (S : CliRunSlotCalleeSpecs M E stdinCap) (maxInitDir wireOutCap : Nat) : Nat :=
  (pathDeltaLive 26 7 + tempFilePostLive addressTryParseDeltaLive) +
    runArmDeltaLive S (pathDeltaLive maxInitDir 16) wireOutCap (sigSliceLive stdinCap)
def cliRunOpenedDeltaPeak {M : AllocCostModel} [HasFineReallocCredit M] {E : CliRunCalleeEnvs}
    {stdinCap : Nat} (S : CliRunSlotCalleeSpecs M E stdinCap)
    (maxInitDir fileCap bundleCap wireOutCap : Nat) : Nat :=
  max (max (pathDeltaPeak 26 7)
        (pathDeltaLive 26 7 + tempFilePostPeak fileCap addressTryParseDeltaPeak))
    ((pathDeltaLive 26 7 + tempFilePostLive addressTryParseDeltaLive) +
      runArmDeltaPeak S (pathDeltaLive maxInitDir 16) (pathDeltaPeak maxInitDir 16)
        bundleCap wireOutCap (sigSliceLive stdinCap) (sigSlicePeak stdinCap))
def cliRunOpenedMaxReq {M : AllocCostModel} [HasFineReallocCredit M] {E : CliRunCalleeEnvs}
    {stdinCap : Nat} (S : CliRunSlotCalleeSpecs M E stdinCap)
    (maxInitDir fileCap bundleCap wireOutCap : Nat) : Nat :=
  max (max (pathMaxReq 26 7) (tempFilePostMaxReq fileCap addressTryParseMaxReq))
    (runArmMaxReq S (pathMaxReq maxInitDir 16) bundleCap wireOutCap (sigSliceMaxReq stdinCap))

theorem cliRunOpened_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : WireLowInterceptHyps M)
    {rd : ReadRule} {E : CliRunCalleeEnvs} {g : RunCall}
    {stdinCap maxInitDir fileCap bundleCap : Nat}
    (S : CliRunSlotCalleeSpecs M E stdinCap) (wireOutCap : Nat)
    (hstdin : g.i.stdin.length ≤ stdinCap)
    (hownCap : ∀ bs,
      rd (runFiles g.i) (pathOf StoresGhost.opened.identity.own.path (utf8 "address")) = .ok bs →
      bs.length ≤ fileCap)
    (hinitDir : ∀ peer dir, g.c = .init peer dir → dir.length ≤ maxInitDir ∧
      (∀ name bs, rd (runFiles g.i) (pathOf dir name) = .ok bs → bs.length ≤ bundleCap)) :
    PhaseCreditSpec M (CliRunOpenedEnv rd E wireOutCap g)
      (cliRunOpenedDeltaCum S maxInitDir fileCap bundleCap wireOutCap)
      (cliRunOpenedDeltaLive S maxInitDir wireOutCap)
      (cliRunOpenedDeltaPeak S maxInitDir fileCap bundleCap wireOutCap)
      (cliRunOpenedMaxReq S maxInitDir fileCap bundleCap wireOutCap) :=
  cliRunOpened_phaseCredit_of_callees hM S wireOutCap
    (path_phaseCredit hM dirDomainCaps_opened_own.path_len_le utf8_address_length_le)
    hownCap hstdin (initBundlePaths_phaseCredit hM hinitDir)
    (fun _ hrest => sigTryFromSlice_phaseCredit hM hLow hrest)

/-- Four stateful wrapper slot envelopes (`initiate`, `encrypt`, `decryptSignal`, `decryptPrekey`)
with `PksmTryFromSliceEnv` wired into `pksmEnv`. -/
structure CliRunWrapperEnvs where
  initEnv : List AllocEvent → Prop
  encEnv : List AllocEvent → Prop
  decSigEnv : List AllocEvent → Prop
  decPkEnv : List AllocEvent → Prop

def CliRunWrapperEnvs.toCalleeEnvs (W : CliRunWrapperEnvs) : CliRunCalleeEnvs where
  initEnv := W.initEnv
  encEnv := W.encEnv
  decSigEnv := W.decSigEnv
  pksmEnv := PksmTryFromSliceEnv
  decPkEnv := W.decPkEnv

structure CliRunWrapperSlotSpecs (M : AllocCostModel) [HasFineReallocCredit M]
    (W : CliRunWrapperEnvs) where
  (initCum initLive initPeak initMaxReq : Nat)
  init_spec : PhaseCreditSpec M W.initEnv initCum initLive initPeak initMaxReq
  init_lp : initLive ≤ initPeak
  (encCum encLive encPeak encMaxReq : Nat)
  enc_spec : PhaseCreditSpec M W.encEnv encCum encLive encPeak encMaxReq
  enc_lp : encLive ≤ encPeak
  (decSigCum decSigLive decSigPeak decSigMaxReq : Nat)
  decSig_spec : PhaseCreditSpec M W.decSigEnv decSigCum decSigLive decSigPeak decSigMaxReq
  decSig_lp : decSigLive ≤ decSigPeak
  (decPkCum decPkLive decPkPeak decPkMaxReq : Nat)
  decPk_spec : PhaseCreditSpec M W.decPkEnv decPkCum decPkLive decPkPeak decPkMaxReq
  decPk_lp : decPkLive ≤ decPkPeak

def CliRunWrapperSlotSpecs.toCalleeSpecs {M : AllocCostModel} [HasFineReallocCredit M]
    {W : CliRunWrapperEnvs} (SW : CliRunWrapperSlotSpecs M W)
    (hM : ModelHyps M) (hLow : WireLowInterceptHyps M) (stdinCap : Nat) :
    CliRunSlotCalleeSpecs M W.toCalleeEnvs stdinCap where
  initCum := SW.initCum
  initLive := SW.initLive
  initPeak := SW.initPeak
  initMaxReq := SW.initMaxReq
  init_spec := SW.init_spec
  init_lp := SW.init_lp
  encCum := SW.encCum
  encLive := SW.encLive
  encPeak := SW.encPeak
  encMaxReq := SW.encMaxReq
  enc_spec := SW.enc_spec
  enc_lp := SW.enc_lp
  decSigCum := SW.decSigCum
  decSigLive := SW.decSigLive
  decSigPeak := SW.decSigPeak
  decSigMaxReq := SW.decSigMaxReq
  decSig_spec := SW.decSig_spec
  decSig_lp := SW.decSig_lp
  pksmCum := pksmSliceCum stdinCap
  pksmLive := pksmSliceLive stdinCap
  pksmPeak := pksmSlicePeak stdinCap
  pksmMaxReq := pksmSliceMaxReq stdinCap
  pksm_spec := fun _ hrest => pksmTryFromSlice_phaseCredit hM hLow hrest
  pksm_lp := pksmSliceLive_le_peak stdinCap
  decPkCum := SW.decPkCum
  decPkLive := SW.decPkLive
  decPkPeak := SW.decPkPeak
  decPkMaxReq := SW.decPkMaxReq
  decPk_spec := SW.decPk_spec
  decPk_lp := SW.decPk_lp

theorem cliRun_slots_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : WireLowInterceptHyps M)
    {rd : ReadRule} {W : CliRunWrapperEnvs} {g : RunCall}
    {stdinCap maxInitDir fileCap bundleCap : Nat}
    (SW : CliRunWrapperSlotSpecs M W) (wireOutCap : Nat)
    (hstdin : g.i.stdin.length ≤ stdinCap)
    (hownCap : ∀ bs,
      rd (runFiles g.i) (pathOf StoresGhost.opened.identity.own.path (utf8 "address")) = .ok bs →
      bs.length ≤ fileCap)
    (hinitDir : ∀ peer dir, g.c = .init peer dir → dir.length ≤ maxInitDir ∧
      (∀ name bs, rd (runFiles g.i) (pathOf dir name) = .ok bs → bs.length ≤ bundleCap)) :
    let S := SW.toCalleeSpecs hM hLow stdinCap
    PhaseCreditSpec M
      (CliRunEnv uuidTryParse rd StoresGhost.opened.identity.own W.toCalleeEnvs wireOutCap g)
      (cliRunDeltaCum S maxInitDir fileCap bundleCap wireOutCap)
      (cliRunDeltaLive S maxInitDir fileCap wireOutCap)
      (cliRunDeltaPeak S maxInitDir fileCap bundleCap wireOutCap)
      (cliRunMaxReq S maxInitDir fileCap bundleCap wireOutCap) :=
  cliRun_phaseCredit hM hLow (SW.toCalleeSpecs hM hLow stdinCap) wireOutCap hstdin hownCap hinitDir

theorem cliRunOpened_slots_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : WireLowInterceptHyps M)
    {rd : ReadRule} {W : CliRunWrapperEnvs} {g : RunCall}
    {stdinCap maxInitDir fileCap bundleCap : Nat}
    (SW : CliRunWrapperSlotSpecs M W) (wireOutCap : Nat)
    (hstdin : g.i.stdin.length ≤ stdinCap)
    (hownCap : ∀ bs,
      rd (runFiles g.i) (pathOf StoresGhost.opened.identity.own.path (utf8 "address")) = .ok bs →
      bs.length ≤ fileCap)
    (hinitDir : ∀ peer dir, g.c = .init peer dir → dir.length ≤ maxInitDir ∧
      (∀ name bs, rd (runFiles g.i) (pathOf dir name) = .ok bs → bs.length ≤ bundleCap)) :
    let S := SW.toCalleeSpecs hM hLow stdinCap
    PhaseCreditSpec M (CliRunOpenedEnv rd W.toCalleeEnvs wireOutCap g)
      (cliRunOpenedDeltaCum S maxInitDir fileCap bundleCap wireOutCap)
      (cliRunOpenedDeltaLive S maxInitDir wireOutCap)
      (cliRunOpenedDeltaPeak S maxInitDir fileCap bundleCap wireOutCap)
      (cliRunOpenedMaxReq S maxInitDir fileCap bundleCap wireOutCap) :=
  cliRunOpened_phaseCredit hM hLow (SW.toCalleeSpecs hM hLow stdinCap) wireOutCap hstdin hownCap hinitDir

def cliRunTightDeltaCum {M : AllocCostModel} [HasFineReallocCredit M] {E : CliRunCalleeEnvs}
    {stdinCap : Nat} (S : CliRunSlotCalleeSpecs M E stdinCap)
    (maxInitDir fileCap bundleCap wireOutCap : Nat) : Nat :=
  (dirGetRuleDeltaCum 26 7 0 fileCap + addressTryParseDeltaCum) +
    runArmTightDeltaCum S (pathDeltaCum maxInitDir 16) bundleCap wireOutCap (sigSliceCum stdinCap)

theorem cliRun_tight_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hT : CliRunTightHyps M) (hLow : WireLowInterceptHyps M)
    {rd : ReadRule} {E : CliRunCalleeEnvs} {g : RunCall}
    {stdinCap maxInitDir fileCap bundleCap : Nat}
    (S : CliRunSlotCalleeSpecs M E stdinCap) (wireOutCap : Nat)
    (hstdin : g.i.stdin.length ≤ stdinCap)
    (hownCap : ∀ bs,
      rd (runFiles g.i) (pathOf StoresGhost.opened.identity.own.path (utf8 "address")) = .ok bs →
      bs.length ≤ fileCap)
    (hinitDir : ∀ peer dir, g.c = .init peer dir → dir.length ≤ maxInitDir ∧
      (∀ name bs, rd (runFiles g.i) (pathOf dir name) = .ok bs → bs.length ≤ bundleCap)) :
    PhaseCreditSpec M (CliRunEnv uuidTryParse rd StoresGhost.opened.identity.own E wireOutCap g)
      (cliRunTightDeltaCum S maxInitDir fileCap bundleCap wireOutCap)
      (cliRunDeltaLive S maxInitDir fileCap wireOutCap)
      (cliRunDeltaPeak S maxInitDir fileCap bundleCap wireOutCap)
      (cliRunMaxReq S maxInitDir fileCap bundleCap wireOutCap) :=
  cliRunOfR0_tight_phaseCredit_of_callees hM hT S wireOutCap
    (r0_tryParse_phaseCredit_of_dirGet hM
      (dirGet_rule_phaseCredit hM rd (runFiles g.i) StoresGhost.opened.identity.own
        (utf8 "address") dirDomainCaps_opened_own utf8_address_length_le hownCap))
    hstdin (initBundlePaths_phaseCredit hM hinitDir)
    (fun _ hrest => sigTryFromSlice_phaseCredit hM hLow hrest)

def cliRunOpenedTightDeltaCum {M : AllocCostModel} [HasFineReallocCredit M] {E : CliRunCalleeEnvs}
    {stdinCap : Nat} (S : CliRunSlotCalleeSpecs M E stdinCap)
    (maxInitDir fileCap bundleCap wireOutCap : Nat) : Nat :=
  (pathDeltaCum 26 7 + tempFilePostCum fileCap addressTryParseDeltaCum) +
    runArmTightDeltaCum S (pathDeltaCum maxInitDir 16) bundleCap wireOutCap (sigSliceCum stdinCap)

theorem cliRunOpened_tight_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hT : CliRunTightHyps M) (hLow : WireLowInterceptHyps M)
    {rd : ReadRule} {E : CliRunCalleeEnvs} {g : RunCall}
    {stdinCap maxInitDir fileCap bundleCap : Nat}
    (S : CliRunSlotCalleeSpecs M E stdinCap) (wireOutCap : Nat)
    (hstdin : g.i.stdin.length ≤ stdinCap)
    (hownCap : ∀ bs,
      rd (runFiles g.i) (pathOf StoresGhost.opened.identity.own.path (utf8 "address")) = .ok bs →
      bs.length ≤ fileCap)
    (hinitDir : ∀ peer dir, g.c = .init peer dir → dir.length ≤ maxInitDir ∧
      (∀ name bs, rd (runFiles g.i) (pathOf dir name) = .ok bs → bs.length ≤ bundleCap)) :
    PhaseCreditSpec M (CliRunOpenedEnv rd E wireOutCap g)
      (cliRunOpenedTightDeltaCum S maxInitDir fileCap bundleCap wireOutCap)
      (cliRunOpenedDeltaLive S maxInitDir wireOutCap)
      (cliRunOpenedDeltaPeak S maxInitDir fileCap bundleCap wireOutCap)
      (cliRunOpenedMaxReq S maxInitDir fileCap bundleCap wireOutCap) :=
  cliRunOfR0_tight_phaseCredit_of_callees hM hT S wireOutCap
    (r0Opened_phaseCredit_of_path hM
      (path_phaseCredit hM dirDomainCaps_opened_own.path_len_le utf8_address_length_le) hownCap)
    hstdin (initBundlePaths_phaseCredit hM hinitDir)
    (fun _ hrest => sigTryFromSlice_phaseCredit hM hLow hrest)

theorem cliRun_slots_tight_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hT : CliRunTightHyps M) (hLow : WireLowInterceptHyps M)
    {rd : ReadRule} {W : CliRunWrapperEnvs}
    {g : RunCall} {stdinCap maxInitDir fileCap bundleCap : Nat}
    (SW : CliRunWrapperSlotSpecs M W) (wireOutCap : Nat)
    (hstdin : g.i.stdin.length ≤ stdinCap)
    (hownCap : ∀ bs,
      rd (runFiles g.i) (pathOf StoresGhost.opened.identity.own.path (utf8 "address")) = .ok bs →
      bs.length ≤ fileCap)
    (hinitDir : ∀ peer dir, g.c = .init peer dir → dir.length ≤ maxInitDir ∧
      (∀ name bs, rd (runFiles g.i) (pathOf dir name) = .ok bs → bs.length ≤ bundleCap)) :
    let S := SW.toCalleeSpecs hM hLow stdinCap
    PhaseCreditSpec M
      (CliRunEnv uuidTryParse rd StoresGhost.opened.identity.own W.toCalleeEnvs wireOutCap g)
      (cliRunTightDeltaCum S maxInitDir fileCap bundleCap wireOutCap)
      (cliRunDeltaLive S maxInitDir fileCap wireOutCap)
      (cliRunDeltaPeak S maxInitDir fileCap bundleCap wireOutCap)
      (cliRunMaxReq S maxInitDir fileCap bundleCap wireOutCap) :=
  cliRun_tight_phaseCredit hM hT hLow (SW.toCalleeSpecs hM hLow stdinCap) wireOutCap hstdin hownCap hinitDir

theorem cliRunOpened_slots_tight_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hT : CliRunTightHyps M) (hLow : WireLowInterceptHyps M)
    {rd : ReadRule} {W : CliRunWrapperEnvs}
    {g : RunCall} {stdinCap maxInitDir fileCap bundleCap : Nat}
    (SW : CliRunWrapperSlotSpecs M W) (wireOutCap : Nat)
    (hstdin : g.i.stdin.length ≤ stdinCap)
    (hownCap : ∀ bs,
      rd (runFiles g.i) (pathOf StoresGhost.opened.identity.own.path (utf8 "address")) = .ok bs →
      bs.length ≤ fileCap)
    (hinitDir : ∀ peer dir, g.c = .init peer dir → dir.length ≤ maxInitDir ∧
      (∀ name bs, rd (runFiles g.i) (pathOf dir name) = .ok bs → bs.length ≤ bundleCap)) :
    let S := SW.toCalleeSpecs hM hLow stdinCap
    PhaseCreditSpec M (CliRunOpenedEnv rd W.toCalleeEnvs wireOutCap g)
      (cliRunOpenedTightDeltaCum S maxInitDir fileCap bundleCap wireOutCap)
      (cliRunOpenedDeltaLive S maxInitDir wireOutCap)
      (cliRunOpenedDeltaPeak S maxInitDir fileCap bundleCap wireOutCap)
      (cliRunOpenedMaxReq S maxInitDir fileCap bundleCap wireOutCap) :=
  cliRunOpened_tight_phaseCredit hM hT hLow (SW.toCalleeSpecs hM hLow stdinCap) wireOutCap
    hstdin hownCap hinitDir

end LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak
