/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
public import LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget

/-!
# Tight `fineCostModel` Credit and Group Bounds for `cliSessionKitDefaultBudgetEnv`

`PhaseCreditSpec` and `PhaseGroupSpec` lemmas for the `DecimalEnv`, `AddrTextValEnv DecimalEnv`,
`PathEnv`, and `DirGetEnv PathEnv (ReadFileRuleEnv rd) rd` envelopes used in
`SessionKitOkCliPlacedBudget.cliSessionKitDefaultBudgetEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux

open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall reserveCap)
open CryptoVerification.SignalSession.Cli (DirGhost ReadRule decimalText pathOf)
open CryptoVerification.SignalSession.Cli.AddressText.Helpers
  (decimalText_device_len_le_three decimalText_device_pos device_zeroExtend32_toNat)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv rustAllocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine (FineScale fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds (fineCostModel_smallMaxReq_eq)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps (DirDomainCaps)
open LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
  (allocBytes1Events_groupSpec fine_rustAlloc_le_28 fine_rustAlloc_le_44 readFileRuleEnv_groupSpec)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (HasFineGroupCredit PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (FreeNonInc ModelHyps PhaseCreditSpec stepEvents_freeOnly_le)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (fineCostModel_freeNonInc)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
  (allocBytes1_fine_phaseCredit_tight fineAllocCapCum fineReadFileCum fineReadFileLive
   fineReadFileMaxReq fineReadFilePeak optLargeCost optLargeCost_fine_of_le
   readFile_rule_fine_phaseCredit_tight)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
  (fineSmallAllocCost_le_1607_of_le_64 fineSmallAllocCost_le_9789_of_le_192
   fineSmallReallocCost_le_9789_of_le_256 rustAllocTightCum rustAllocTightCum_fine_le_738)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.AddressText.PlacedBudgetAux
  (addrDecReserveEvents addrDecReserveEvents_not_grow addrDotReserveEvents addrToOwnedEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget
  (DecimalEnv decimalEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a
  (DirGetAfterReadEnv DirGetEnv DirGetErrAllocEnv DirGetMissEnv DirGetPathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget
  (PathEnv pathAppendNameEvents pathEvents pathPushSlashEvents pathSlashCap pathToOwnedEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget (AddrTextValEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (doReserveEvents)

/-- Appending `FreeOnlyEvs` preserves `PhaseCreditSpec M E c l p r` under `FreeNonInc M`. -/
theorem seq_freeOnly_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hF : FreeNonInc M) {E : List AllocEvent → Prop} {c l p r : Nat}
    (h : PhaseCreditSpec M E c l p r) :
    PhaseCreditSpec M (SeqEnv E FreeOnlyEvs) c l p r where
  req_align evs hE ev hev := by
    rcases hE with h1 | ⟨evs₁, evs₂, rfl, h1, h2⟩
    · exact h.req_align evs h1 ev hev
    · rcases List.mem_append.mp hev with he1 | he2
      · exact h.req_align evs₁ h1 ev he1
      · obtain ⟨al, sz, rfl⟩ := h2 ev he2
        exact ⟨Nat.zero_le r, Nat.le_refl 16⟩
  credit_le st0 {_} hE := by
    rcases hE with h1 | ⟨evs₁, evs₂, rfl, h1, h2⟩
    · exact h.credit_le st0 h1
    · rw [M.stepEvents_append evs₁ evs₂ st0]
      obtain ⟨hc₁, hl₁, hp₁⟩ := h.credit_le st0 h1
      obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_freeOnly_le hF h2 (M.stepEvents evs₁ st0)
      exact ⟨Nat.le_trans hc₂ hc₁, Nat.le_trans hl₂ hl₁, Nat.le_trans hp₂ hp₁⟩

private theorem fineAllocCapCum_le_readFileCum_local (fc : Nat) :
    fineAllocCapCum fc ≤ fineReadFileCum fc := by
  unfold fineAllocCapCum fineReadFileCum
  split_ifs <;> omega

private theorem optLargeCost_fine_le_readFileLive_local (fc : Nat) :
    optLargeCost fineCostModel fc ≤ fineReadFileLive fc := by
  unfold fineReadFileLive
  split
  · rename_i hle
    rw [optLargeCost_fine_of_le (Nat.le_trans hle (by decide))]
  · exact Nat.le_max_left _ _

private theorem fineReadFileLive_le_peak_local (fc : Nat) :
    fineReadFileLive fc ≤ fineReadFilePeak fc := by
  unfold fineReadFileLive fineReadFilePeak
  split
  · exact Nat.le_refl 0
  · exact Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans (by decide) (Nat.le_max_right _ _)⟩

private theorem le_fineReadFileMaxReq_local (fc : Nat) :
    fc ≤ fineReadFileMaxReq fc := by
  unfold fineReadFileMaxReq
  split_ifs <;> omega

/-- For every `device : BitVec 8`, `decimalEvents (device.zeroExtend 32)` emits `rustAllocEvents 8 1`
(`1 ≤ |decimalText| ≤ 3`, so only the first `pushByteStep 0 0` allocates `reserveCap 0 0 1 = 8` B). -/
theorem decimalEvents_device_eq (device : BitVec 8) :
    decimalEvents (device.zeroExtend 32) = rustAllocEvents 8 1 := by
  have hpos : 0 < (decimalText (device.zeroExtend 32).toNat).length := by
    rw [device_zeroExtend32_toNat]; exact decimalText_device_pos device
  have hle3 : (decimalText (device.zeroExtend 32).toNat).length ≤ 3 := by
    rw [device_zeroExtend32_toNat]; exact decimalText_device_len_le_three device
  unfold decimalEvents
  match hlen : (decimalText (device.zeroExtend 32).toNat).length with
  | 0 => omega
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | _ + 4 => omega

/-- Tight `fineCostModel` `PhaseCreditSpec` for `DecimalEnv (device.zeroExtend 32)` (`738` B). -/
theorem decimal_device_fine_phaseCredit_tight (device : BitVec 8) :
    PhaseCreditSpec fineCostModel (DecimalEnv (device.zeroExtend 32)) 738 0 0 8 := by
  have ha := PhaseCreditSpec.rustAlloc_small fineCostModel
    (req := 8) (al := 1) (by decide) (by decide)
    (by rw [fineCostModel_smallMaxReq_eq]; decide)
  have hc : HasFineReallocCredit.smallAllocCost fineCostModel 8 ≤ 738 := by
    have h1 := rustAllocTightCum_fine_le_738 (req := 8) (by decide)
    unfold rustAllocTightCum at h1
    rw [fineCostModel_smallMaxReq_eq] at h1
    simpa using h1
  exact (ha.of_imp (fun _ h => by
    unfold DecimalEnv at h
    rw [h, decimalEvents_device_eq device])).mono
    hc (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 8)

/-- Regime-free `PhaseCreditSpec M` for `DecimalEnv (device.zeroExtend 32)`. -/
theorem decimal_device_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (device : BitVec 8) :
    PhaseCreditSpec M (DecimalEnv (device.zeroExtend 32))
      (2 * 8 + 9539) (8 + 8195) (8 + 8195) 8 :=
  (PhaseCreditSpec.rustAlloc_aff hM (req := 8) (al := 1) (by decide)).of_imp
    (fun _ h => by unfold DecimalEnv at h; rw [h, decimalEvents_device_eq device])

/-- For `rem.name.length ≤ 40`, `reserveCap rem.name.length rem.name.length 1` already covers
`(rem.name ++ ['.']).length + (decimalText _).length`, so `addrDecReserveEvents` is `[]`. -/
theorem addrDecReserveEvents_eq_nil_of_le_40 (rem : AddrVal)
    (hname : rem.name.length ≤ 40) :
    addrDecReserveEvents rem.name rem.device = [] := by
  have hdec : (decimalText (rem.device.zeroExtend 32).toNat).length ≤ 3 := by
    rw [device_zeroExtend32_toNat]; exact decimalText_device_len_le_three rem.device
  have hrc_bounds :
      (rem.name ++ [0x2e#8]).length + (decimalText (rem.device.zeroExtend 32).toNat).length ≤
        reserveCap rem.name.length rem.name.length 1 ∧
      reserveCap rem.name.length rem.name.length 1 ≤ 80 := by
    rw [List.length_append, List.length_singleton]
    unfold reserveCap
    omega
  have htoNat :
      (BitVec.ofNat 64 (reserveCap rem.name.length rem.name.length 1)).toNat =
        reserveCap rem.name.length rem.name.length 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hnot :
      ¬ ((BitVec.ofNat 64 (reserveCap rem.name.length rem.name.length 1)).toNat <
          (rem.name ++ [0x2e#8]).length + (decimalText (rem.device.zeroExtend 32).toNat).length) := by
    rw [htoNat]
    omega
  exact addrDecReserveEvents_not_grow rem.name rem.device hnot

/-- Tight `fineCostModel` `PhaseCreditSpec` for `AddrTextValEnv DecimalEnv rem`
(`rem.name.length ≤ 40`): `Δcum = 11,265` B (`738 + 9,789 + 738 + 0`), `Δlive = 0`, `Δpeak = 0`,
`maxReq = 80`. -/
theorem addrTextValEnv_decimal_fine_phaseCredit_tight (rem : AddrVal)
    (hname : rem.name.length ≤ 40) :
    PhaseCreditSpec fineCostModel (AddrTextValEnv DecimalEnv rem) 11265 0 0 80 := by
  unfold AddrTextValEnv
  have h1 : PhaseCreditSpec fineCostModel (· = addrToOwnedEvents rem.name) 738 0 0 40 := by
    unfold addrToOwnedEvents
    split_ifs with hz
    · exact (PhaseCreditSpec.nil fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    · have hpos : 0 < rem.name.length := Nat.pos_of_ne_zero hz
      have ha := PhaseCreditSpec.rustAlloc_small fineCostModel
        (req := rem.name.length) (al := 1) (by decide) hpos
        (by rw [fineCostModel_smallMaxReq_eq]; omega)
      have hc : HasFineReallocCredit.smallAllocCost fineCostModel rem.name.length ≤ 738 := by
        have h738 := rustAllocTightCum_fine_le_738 (req := rem.name.length) (by omega)
        unfold rustAllocTightCum at h738
        rw [fineCostModel_smallMaxReq_eq] at h738
        have hsm : rem.name.length ≤ 135167 := by omega
        simpa [hsm] using h738
      exact ha.mono hc (Nat.le_refl 0) (Nat.le_refl 0) hname
  have h2 : PhaseCreditSpec fineCostModel (· = addrDotReserveEvents rem.name) 9789 0 0 80 := by
    unfold addrDotReserveEvents
    have htoNat : (BitVec.ofNat 64 rem.name.length).toNat = rem.name.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hrc : 8 ≤ reserveCap rem.name.length rem.name.length 1 ∧
        reserveCap rem.name.length rem.name.length 1 ≤ 80 := by
      unfold reserveCap; omega
    by_cases hz : rem.name.length = 0
    · have hb0 : BitVec.ofNat 64 rem.name.length = 0#64 := by simp [hz]
      have hd : doReserveEvents (DoReserveCall.mk 0#64 (BitVec.ofNat 64 rem.name.length) 0#64 rem.name 1) =
          rustAllocEvents (reserveCap rem.name.length rem.name.length 1) 1 := by
        unfold doReserveEvents; dsimp only; rw [htoNat]; simp only [hb0, ↓reduceIte]
      exact ((PhaseCreditSpec.rustAlloc_small fineCostModel
        (req := reserveCap rem.name.length rem.name.length 1) (al := 1) (by decide)
        (by omega) (by rw [fineCostModel_smallMaxReq_eq]; omega)).of_imp
        (fun _ heq => by rw [heq, hd])).mono
        (fineSmallAllocCost_le_9789_of_le_192 (by omega))
        (Nat.le_refl 0) (Nat.le_refl 0) hrc.2
    · have hpos : 0 < rem.name.length := Nat.pos_of_ne_zero hz
      have hne0 : BitVec.ofNat 64 rem.name.length ≠ 0#64 := by
        intro heq
        have ht := congrArg BitVec.toNat heq
        rw [htoNat] at ht
        exact hz ht
      have hd : doReserveEvents (DoReserveCall.mk 0#64 (BitVec.ofNat 64 rem.name.length) 0#64 rem.name 1) =
          rustReallocEvents rem.name.length (reserveCap rem.name.length rem.name.length 1) 1 := by
        unfold doReserveEvents; dsimp only; rw [htoNat]; simp only [hne0, ↓reduceIte]
      exact ((PhaseCreditSpec.rustRealloc_small_small fineCostModel
        (old := rem.name.length) (new := reserveCap rem.name.length rem.name.length 1) (al := 1)
        (by decide) (by omega) hpos
        (by rw [fineCostModel_smallMaxReq_eq]; omega)
        (by omega) (by rw [fineCostModel_smallMaxReq_eq]; omega)).of_imp
        (fun _ heq => by rw [heq, hd])).mono
        (fineSmallReallocCost_le_9789_of_le_256 (by omega))
        (Nat.le_refl 0) (Nat.le_refl 0) hrc.2
  have h3 := decimal_device_fine_phaseCredit_tight rem.device
  have h4 : PhaseCreditSpec fineCostModel
      (SeqEnv (· = addrDecReserveEvents rem.name rem.device) FreeOnlyEvs) 0 0 0 0 :=
    seq_freeOnly_phaseCredit fineCostModel_freeNonInc
      (PhaseCreditSpec.of_eq_nil (fun _ heq => by
        rw [heq, addrDecReserveEvents_eq_nil_of_le_40 rem hname]))
  exact (h1.seq (h2.seq (h3.seq h4))).mono (by decide) (by decide) (by decide) (by decide)

/-- Generic `PhaseGroupSpec M` (`9 * FineScale`) for `AddrTextValEnv DecimalEnv rem` (`≤ 40` B). -/
theorem addrTextValEnv_decimal_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (rem : AddrVal) (hrem : rem.name.length ≤ 40) :
    PhaseGroupSpec M (AddrTextValEnv DecimalEnv rem) (9 * FineScale) := by
  unfold AddrTextValEnv
  have s1 : PhaseGroupSpec M (· = addrToOwnedEvents rem.name) (3 * FineScale) := by
    unfold addrToOwnedEvents
    split
    · exact (PhaseGroupSpec.nil M).mono (Nat.zero_le _)
    · exact PhaseGroupSpec.rustAlloc_any M rem.name.length 1
  have s2 : PhaseGroupSpec M (· = addrDotReserveEvents rem.name) (3 * FineScale) := by
    unfold addrDotReserveEvents doReserveEvents
    dsimp only
    split
    · exact PhaseGroupSpec.rustAlloc_any M _ 1
    · exact PhaseGroupSpec.rustRealloc_any M _ _ 1
  have s3 : PhaseGroupSpec M (DecimalEnv (rem.device.zeroExtend 32)) (3 * FineScale) :=
    (PhaseGroupSpec.rustAlloc_any M 8 1).of_imp
      (fun _ h => by unfold DecimalEnv at h; rw [h, decimalEvents_device_eq rem.device])
  have s4 : PhaseGroupSpec M
      (SeqEnv (· = addrDecReserveEvents rem.name rem.device) FreeOnlyEvs) 0 := by
    have hnil : PhaseGroupSpec M (· = addrDecReserveEvents rem.name rem.device) 0 :=
      (PhaseGroupSpec.nil M).of_imp
        (fun _ h => by rw [h, addrDecReserveEvents_eq_nil_of_le_40 rem hrem])
    exact (hnil.seq (PhaseGroupSpec.freeOnly M)).mono (Nat.le_refl 0)
  exact (s1.seq (s2.seq (s3.seq s4))).mono (by omega)

/-- Tight `fineCostModel` `PhaseGroupSpec` (`6 * FineScale`) for `AddrTextValEnv DecimalEnv rem`
(`16,659 + 3 * FineScale + 11,056 = 224,323 ≤ 6 * FineScale = 393,216`). -/
theorem addrTextValEnv_decimal_fine_groupSpec (rem : AddrVal) (hrem : rem.name.length ≤ 40) :
    PhaseGroupSpec fineCostModel (AddrTextValEnv DecimalEnv rem) (6 * FineScale) := by
  unfold AddrTextValEnv
  have s1 : PhaseGroupSpec fineCostModel (· = addrToOwnedEvents rem.name) 16659 := by
    unfold addrToOwnedEvents
    split
    · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    · exact fine_rustAlloc_le_44 (by decide) (Nat.le_trans hrem (by decide))
  have s2 : PhaseGroupSpec fineCostModel (· = addrDotReserveEvents rem.name) (3 * FineScale) := by
    unfold addrDotReserveEvents doReserveEvents
    dsimp only
    split
    · exact PhaseGroupSpec.rustAlloc_any fineCostModel _ 1
    · exact PhaseGroupSpec.rustRealloc_any fineCostModel _ _ 1
  have s3 : PhaseGroupSpec fineCostModel (DecimalEnv (rem.device.zeroExtend 32)) 11056 :=
    (fine_rustAlloc_le_28 (sz := 8) (al := 1) (by decide) (by decide)).of_imp
      (fun _ h => by unfold DecimalEnv at h; rw [h, decimalEvents_device_eq rem.device])
  have s4 : PhaseGroupSpec fineCostModel
      (SeqEnv (· = addrDecReserveEvents rem.name rem.device) FreeOnlyEvs) 0 := by
    have hnil : PhaseGroupSpec fineCostModel (· = addrDecReserveEvents rem.name rem.device) 0 :=
      (PhaseGroupSpec.nil fineCostModel).of_imp
        (fun _ h => by rw [h, addrDecReserveEvents_eq_nil_of_le_40 rem hrem])
    exact (hnil.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono (Nat.le_refl 0)
  exact (s1.seq (s2.seq (s3.seq s4))).mono (by decide)

/-- Tight `fineCostModel` `PhaseCreditSpec` for `PathEnv dir name`
(`dir.length ≤ 64`, `name.length ≤ 64`): `Δcum = 21,185` B, `Δlive = 0`, `Δpeak = 0`,
`maxReq = 256`. -/
theorem pathEnv_fine_phaseCredit_tight {dir name : List (BitVec 8)}
    (hdir : dir.length ≤ 64) (hname : name.length ≤ 64) :
    PhaseCreditSpec fineCostModel (PathEnv dir name) 21185 0 0 256 := by
  unfold PathEnv pathEvents
  by_cases hz : dir.length = 0
  · have h1 : pathToOwnedEvents dir.length = [] := by unfold pathToOwnedEvents; simp [hz]
    have hc1 : pathSlashCap 0 = 8 := by unfold pathSlashCap reserveCap; decide
    have h2 : pathPushSlashEvents dir.length = rustAllocEvents 8 1 := by
      unfold pathPushSlashEvents; simp [hz, hc1]
    have s2 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 8 1) 738 0 0 8 := by
      have ha := PhaseCreditSpec.rustAlloc_small fineCostModel
        (req := 8) (al := 1) (by decide) (by decide)
        (by rw [fineCostModel_smallMaxReq_eq]; decide)
      have hc : HasFineReallocCredit.smallAllocCost fineCostModel 8 ≤ 738 := by
        have h738 := rustAllocTightCum_fine_le_738 (req := 8) (by decide)
        unfold rustAllocTightCum at h738
        rw [fineCostModel_smallMaxReq_eq] at h738
        simpa using h738
      exact ha.mono hc (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 8)
    have s3 : PhaseCreditSpec fineCostModel (· = pathAppendNameEvents 0 name.length) 9789 0 0 256 := by
      unfold pathAppendNameEvents
      simp only [Nat.zero_add, hc1]
      split_ifs with hlt
      · have hrc : 8 ≤ reserveCap 8 1 name.length ∧ reserveCap 8 1 name.length ≤ 256 := by
          unfold reserveCap; omega
        exact (PhaseCreditSpec.rustRealloc_small_small fineCostModel
          (old := 8) (new := reserveCap 8 1 name.length) (al := 1)
          (by decide) (by omega) (by decide)
          (by rw [fineCostModel_smallMaxReq_eq]; decide)
          (by omega) (by rw [fineCostModel_smallMaxReq_eq]; omega)).mono
          (fineSmallReallocCost_le_9789_of_le_256 hrc.2)
          (Nat.le_refl 0) (Nat.le_refl 0) hrc.2
      · exact (PhaseCreditSpec.nil fineCostModel).mono
          (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    exact ((s2.concat s3).of_imp (fun _ heq => by
      rw [heq, h1, h2, List.nil_append]
      simp only [hz]
      exact ⟨rustAllocEvents 8 1, pathAppendNameEvents 0 name.length, rfl, rfl, rfl⟩)).mono
      (by decide) (by decide) (by decide) (by decide)
  · have hpos : 0 < dir.length := Nat.pos_of_ne_zero hz
    have hc1 : 8 ≤ pathSlashCap dir.length ∧ pathSlashCap dir.length ≤ 128 := by
      unfold pathSlashCap reserveCap; omega
    have s1 : PhaseCreditSpec fineCostModel (· = pathToOwnedEvents dir.length) 1607 0 0 64 := by
      unfold pathToOwnedEvents
      simp only [hz, ↓reduceIte]
      exact (PhaseCreditSpec.rustAlloc_small fineCostModel
        (req := dir.length) (al := 1)
        (by decide) hpos (by rw [fineCostModel_smallMaxReq_eq]; omega)).mono
        (fineSmallAllocCost_le_1607_of_le_64 hdir)
        (Nat.le_refl 0) (Nat.le_refl 0) hdir
    have s2 : PhaseCreditSpec fineCostModel (· = pathPushSlashEvents dir.length) 9789 0 0 128 := by
      unfold pathPushSlashEvents
      simp only [hz, ↓reduceIte]
      exact (PhaseCreditSpec.rustRealloc_small_small fineCostModel
        (old := dir.length) (new := pathSlashCap dir.length) (al := 1)
        (by decide) (by omega) hpos
        (by rw [fineCostModel_smallMaxReq_eq]; omega)
        (by omega) (by rw [fineCostModel_smallMaxReq_eq]; omega)).mono
        (fineSmallReallocCost_le_9789_of_le_256 (by omega))
        (Nat.le_refl 0) (Nat.le_refl 0) hc1.2
    have s3 : PhaseCreditSpec fineCostModel
        (· = pathAppendNameEvents dir.length name.length) 9789 0 0 256 := by
      unfold pathAppendNameEvents
      dsimp only
      split_ifs with hlt
      · have hrc : 8 ≤ reserveCap (pathSlashCap dir.length) (dir.length + 1) name.length ∧
            reserveCap (pathSlashCap dir.length) (dir.length + 1) name.length ≤ 256 := by
          unfold reserveCap; omega
        exact (PhaseCreditSpec.rustRealloc_small_small fineCostModel
          (old := pathSlashCap dir.length)
          (new := reserveCap (pathSlashCap dir.length) (dir.length + 1) name.length) (al := 1)
          (by decide) (by omega) (by omega)
          (by rw [fineCostModel_smallMaxReq_eq]; omega)
          (by omega) (by rw [fineCostModel_smallMaxReq_eq]; omega)).mono
          (fineSmallReallocCost_le_9789_of_le_256 hrc.2)
          (Nat.le_refl 0) (Nat.le_refl 0) hrc.2
      · exact (PhaseCreditSpec.nil fineCostModel).mono
          (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    exact (s1.concat (s2.concat s3)).of_imp (fun _ heq =>
      ⟨pathToOwnedEvents dir.length,
        pathPushSlashEvents dir.length ++ pathAppendNameEvents dir.length name.length,
        heq, rfl,
        ⟨pathPushSlashEvents dir.length, pathAppendNameEvents dir.length name.length,
          rfl, rfl, rfl⟩⟩) |>.mono (by decide) (by decide) (by decide) (by decide)

/-- Tight `fineCostModel` `PhaseCreditSpec` for `DirGetEnv PathEnv (ReadFileRuleEnv rd) rd`
(`dir.path.length ≤ 64`, `name.length ≤ 64`):
on `.error ()`, `ReadFileRuleEnv` is `[]` and `DirGetErrAllocEnv` allocates `22` B (`738` B),
while on `.ok bs`, `DirGetErrAllocEnv` is `[]` and `ReadFileRuleEnv` uses `fineReadFileCum fc`. -/
theorem dirGetEnv_path_readFile_fine_phaseCredit_tight
    (rd : ReadRule) (F0 : FsFiles) (dir : DirGhost) (name : List (BitVec 8))
    {maxEntries maxVal fileCap : Nat}
    (hdc : DirDomainCaps 64 maxEntries maxVal dir)
    (hname : name.length ≤ 64)
    (hcap : ∀ bs, rd F0 (pathOf dir.path name) = .ok bs → bs.length ≤ fileCap) :
    let fc := max maxVal fileCap
    PhaseCreditSpec fineCostModel
      (DirGetEnv PathEnv (ReadFileRuleEnv rd) rd F0 dir name)
      (21185 + max 738 (fineReadFileCum fc))
      (fineReadFileLive fc)
      (fineReadFilePeak fc)
      (max 256 (fineReadFileMaxReq fc)) := by
  dsimp only
  unfold DirGetEnv
  cases hfind : dir.changed.find? (fun e => e.1 == name) with
  | some e =>
    have hmem : e ∈ dir.changed := List.mem_of_find?_eq_some hfind
    have hv : e.2.length ≤ max maxVal fileCap :=
      Nat.le_trans (hdc.changed_val_le e.1 e.2 hmem) (Nat.le_max_left _ _)
    exact (allocBytes1_fine_phaseCredit_tight hv).mono
      (Nat.le_trans (fineAllocCapCum_le_readFileCum_local (max maxVal fileCap))
        (Nat.le_trans (Nat.le_max_right 738 _) (Nat.le_add_left _ 21185)))
      (optLargeCost_fine_le_readFileLive_local (max maxVal fileCap))
      (Nat.le_trans (optLargeCost_fine_le_readFileLive_local (max maxVal fileCap))
        (fineReadFileLive_le_peak_local (max maxVal fileCap)))
      (Nat.le_trans (le_fineReadFileMaxReq_local (max maxVal fileCap)) (Nat.le_max_right 256 _))
  | none =>
    unfold DirGetMissEnv
    have hp : PhaseCreditSpec fineCostModel
        (DirGetPathEnv PathEnv dir.path name) 21185 0 0 256 := by
      unfold DirGetPathEnv
      split_ifs
      · have hab := allocBytes1_fine_phaseCredit_tight hname
        rw [optLargeCost_fine_of_le (by decide)] at hab
        exact hab.mono (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
      · exact pathEnv_fine_phaseCredit_tight hdc.path_len_le hname
    cases hrd : rd F0 (pathOf dir.path name) with
    | error u =>
      cases u
      have hr0 : PhaseCreditSpec fineCostModel
          (ReadFileRuleEnv rd F0 (pathOf dir.path name)) 0 0 0 0 :=
        PhaseCreditSpec.of_eq_nil (fun _ h => by unfold ReadFileRuleEnv at h; rw [hrd] at h; exact h)
      have herr22 : PhaseCreditSpec fineCostModel
          (DirGetAfterReadEnv rd F0 (pathOf dir.path name)) 738 0 0 22 := by
        unfold DirGetAfterReadEnv DirGetErrAllocEnv
        rw [hrd]
        have ha22 := PhaseCreditSpec.rustAlloc_small fineCostModel
          (req := 22) (al := 1) (by decide) (by decide)
          (by rw [fineCostModel_smallMaxReq_eq]; decide)
        have hc22 : HasFineReallocCredit.smallAllocCost fineCostModel 22 ≤ 738 := by
          have h738 := rustAllocTightCum_fine_le_738 (req := 22) (by decide)
          unfold rustAllocTightCum at h738
          rw [fineCostModel_smallMaxReq_eq] at h738
          simpa using h738
        exact seq_freeOnly_phaseCredit fineCostModel_freeNonInc
          (ha22.mono hc22 (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 22))
      exact (hp.seq (hr0.seq herr22)).mono
        (by omega) (Nat.zero_le _) (Nat.zero_le _)
        (Nat.max_le.mpr ⟨Nat.le_max_left 256 _,
          Nat.le_trans (by decide : max 0 22 ≤ 256) (Nat.le_max_left 256 _)⟩)
    | ok bs =>
      have hrOk := readFile_rule_fine_phaseCredit_tight rd F0 (pathOf dir.path name)
        (fc := max maxVal fileCap)
        (fun bs' h' => Nat.le_trans (hcap bs' h') (Nat.le_max_right maxVal fileCap))
      have herr0 : PhaseCreditSpec fineCostModel
          (DirGetAfterReadEnv rd F0 (pathOf dir.path name)) 0 0 0 0 := by
        unfold DirGetAfterReadEnv DirGetErrAllocEnv
        rw [hrd]
        exact seq_freeOnly_phaseCredit fineCostModel_freeNonInc (PhaseCreditSpec.nil fineCostModel)
      have hr_seq := hrOk.seq herr0
      exact (hp.seq hr_seq).mono
        (by omega)
        (by omega)
        (Nat.max_le.mpr ⟨Nat.zero_le _,
          Nat.le_of_eq (Nat.zero_add _) |>.trans
            (Nat.max_le.mpr ⟨Nat.le_refl _,
              Nat.le_trans (Nat.add_zero _).le (fineReadFileLive_le_peak_local (max maxVal fileCap))⟩)⟩)
        (Nat.max_le.mpr ⟨Nat.le_max_left 256 _,
          Nat.le_trans (Nat.max_eq_left (Nat.zero_le _)).le (Nat.le_max_right 256 _)⟩)

/-- `PhaseGroupSpec M` (`39 * FineScale`) for `DirGetEnv PathEnv (ReadFileRuleEnv rd) rd`. -/
theorem dirGetEnv_path_readFile_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (rd : ReadRule) (F0 : FsFiles) (dir : DirGhost) (name : List (BitVec 8)) :
    PhaseGroupSpec M (DirGetEnv PathEnv (ReadFileRuleEnv rd) rd F0 dir name)
      (39 * FineScale) := by
  have hPath : PhaseGroupSpec M (DirGetPathEnv PathEnv dir.path name) (9 * FineScale) := by
    unfold DirGetPathEnv
    split
    · exact (allocBytes1Events_groupSpec M name).mono (by omega)
    · unfold PathEnv pathEvents
      have p1 : PhaseGroupSpec M (· = pathToOwnedEvents dir.path.length) (3 * FineScale) := by
        unfold pathToOwnedEvents
        split
        · exact (PhaseGroupSpec.nil M).mono (Nat.zero_le _)
        · exact PhaseGroupSpec.rustAlloc_any M _ 1
      have p2 : PhaseGroupSpec M (· = pathPushSlashEvents dir.path.length) (3 * FineScale) := by
        unfold pathPushSlashEvents
        split
        · exact PhaseGroupSpec.rustAlloc_any M _ 1
        · exact PhaseGroupSpec.rustRealloc_any M _ _ 1
      have p3 : PhaseGroupSpec M
          (· = pathAppendNameEvents dir.path.length name.length) (3 * FineScale) := by
        unfold pathAppendNameEvents
        dsimp only
        split
        · exact PhaseGroupSpec.rustRealloc_any M _ _ 1
        · exact (PhaseGroupSpec.nil M).mono (Nat.zero_le _)
      exact (p1.concat (p2.concat p3)).of_imp (fun _ heq =>
        ⟨_, _, heq, rfl, ⟨_, _, rfl, rfl, rfl⟩⟩) |>.mono (by omega)
  unfold DirGetEnv
  cases dir.changed.find? (fun e => e.1 == name) with
  | some e =>
    exact (allocBytes1Events_groupSpec M e.2).mono (by omega)
  | none =>
    unfold DirGetMissEnv
    cases hrd : rd F0 (pathOf dir.path name) with
    | error u =>
      cases u
      have hr0 : PhaseGroupSpec M (ReadFileRuleEnv rd F0 (pathOf dir.path name)) 0 :=
        (PhaseGroupSpec.nil M).of_imp
          (fun _ h => by unfold ReadFileRuleEnv at h; rw [hrd] at h; exact h)
      have herr : PhaseGroupSpec M
          (DirGetAfterReadEnv rd F0 (pathOf dir.path name)) (3 * FineScale) := by
        unfold DirGetAfterReadEnv DirGetErrAllocEnv
        rw [hrd]
        exact ((PhaseGroupSpec.rustAlloc_any M 22 1).seq
          (PhaseGroupSpec.freeOnly M)).mono (by omega)
      exact (hPath.seq (hr0.seq herr)).mono (by omega)
    | ok _ =>
      have hrOk := readFileRuleEnv_groupSpec M rd F0 (pathOf dir.path name)
      have herr0 : PhaseGroupSpec M
          (DirGetAfterReadEnv rd F0 (pathOf dir.path name)) 0 := by
        unfold DirGetAfterReadEnv DirGetErrAllocEnv
        rw [hrd]
        exact ((PhaseGroupSpec.nil M).seq (PhaseGroupSpec.freeOnly M)).mono (Nat.le_refl 0)
      exact (hPath.seq (hrOk.seq herr0)).mono (by omega)

end LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux
