/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.Top
public import Symbolic.BugInjection.Proofs.Common443.CompMemoInjGtDraws
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvIni
public import Symbolic.BugInjection.Proofs.Fixtures.Cheval26SmallSubgroupTorsionComp

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
namespace Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.CompMemoInjGt Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitComp
attribute [local irreducible] Symbolic.BugInjection.hexBytes
def bundleBytes : HwBytes :=
  match (Witnesses.Cheval26SmallSubgroupHighBitComp.trace[0]? : Option MachineEvent) with
  | some (.recv b) => b
  | _ => []
def call0RngEvents : List MachineEvent := (Witnesses.Cheval26SmallSubgroupHighBitComp.trace.take 35).tail
theorem trace_take_35_eq : Witnesses.Cheval26SmallSubgroupHighBitComp.trace.take 35 = .recv bundleBytes :: call0RngEvents := rfl
theorem torsionComp_trace_take_35_eq : Witnesses.Cheval26SmallSubgroupTorsionComp.trace.take 35 = .recv bundleBytes :: call0RngEvents := rfl
theorem torsionComp_trace_getElem?_35 : Witnesses.Cheval26SmallSubgroupTorsionComp.trace[35]? = some (.pt ptMsg35) := rfl
def bundleChars : List Char := chars_of_hex_def bundleBytes
theorem bundleBytes_eq_hex : bundleBytes = hexBytes (str_of_hex_def bundleBytes) := rfl
theorem bundleStr_eq : (str_of_hex_def bundleBytes) = String.ofList bundleChars := rfl
def bundleFast : HwBytes := hexBytes.go hexDigit bundleChars
theorem bundleBytes_eq_fast : bundleBytes = bundleFast := by change bundleBytes = hexBytes.go hexDigit bundleChars; rw [bundleBytes_eq_hex, bundleStr_eq, hexBytes_ofList]
theorem bundleFast_getElem4_ne_one : bundleFast[4]? ≠ some 1#8 := by decide +kernel
theorem bundleBytes_getElem4_ne_one : bundleBytes[4]? ≠ some 1#8 := by rw [bundleBytes_eq_fast]; exact bundleFast_getElem4_ne_one
theorem call0RngEvents_length : call0RngEvents.length = 34 := rfl
theorem call0RngEvents_kind : ∀ e ∈ call0RngEvents, eventKind e = .rng := by decide
def rngEkBytes : HwBytes :=
  match (Witnesses.Cheval26SmallSubgroupHighBitComp.trace[1]? : Option MachineEvent) with
  | some (.rng b) => b
  | _ => []
def rngDhsBytes : HwBytes :=
  match (Witnesses.Cheval26SmallSubgroupHighBitComp.trace[34]? : Option MachineEvent) with
  | some (.rng b) => b
  | _ => []
theorem call0RngEvents_take_1_eq : call0RngEvents.take 1 = [.rng rngEkBytes] := rfl
theorem call0RngEvents_drop_33_eq : call0RngEvents.drop 33 = [.rng rngDhsBytes] := rfl
def rngEkChars : List Char := chars_of_hex_def rngEkBytes
theorem rngEkBytes_eq_hex : rngEkBytes = hexBytes (str_of_hex_def rngEkBytes) := rfl
theorem rngEkStr_eq : (str_of_hex_def rngEkBytes) = String.ofList rngEkChars := rfl
theorem rngEkBytes_length : rngEkBytes.length = 32 := by have h : rngEkBytes = hexBytes.go hexDigit rngEkChars := (by rw [rngEkBytes_eq_hex, rngEkStr_eq, hexBytes_ofList]); rw [h]; rfl
def rngDhsChars : List Char := chars_of_hex_def rngDhsBytes
theorem rngDhsBytes_eq_hex : rngDhsBytes = hexBytes (str_of_hex_def rngDhsBytes) := rfl
theorem rngDhsStr_eq : (str_of_hex_def rngDhsBytes) = String.ofList rngDhsChars := rfl
theorem rngDhsBytes_length : rngDhsBytes.length = 32 := by have h : rngDhsBytes = hexBytes.go hexDigit rngDhsChars := (by rw [rngDhsBytes_eq_hex, rngDhsStr_eq, hexBytes_ofList]); rw [h]; rfl
def ptMsg35Chars : List Char := chars_of_hex_def ptMsg35
theorem ptMsg35_eq_hex : ptMsg35 = hexBytes (str_of_hex_def ptMsg35) := rfl
theorem ptMsg35Str_eq : (str_of_hex_def ptMsg35) = String.ofList ptMsg35Chars := rfl
theorem ptMsg35_length : ptMsg35.length = 9 := by have h : ptMsg35 = hexBytes.go hexDigit ptMsg35Chars := (by rw [ptMsg35_eq_hex, ptMsg35Str_eq, hexBytes_ofList]); rw [h]; rfl
theorem call0RngEvents_take_1_gt_9 : ∀ e ∈ call0RngEvents.take 1, 9 < (Common443.Census443Defs.eventBytes e).length := by
  intro e he; rw [call0RngEvents_take_1_eq, List.mem_singleton] at he; subst he
  show 9 < rngEkBytes.length
  rw [rngEkBytes_length]
  decide
theorem call0RngEvents_drop_33_gt_9 : ∀ e ∈ call0RngEvents.drop 33, 9 < (Common443.Census443Defs.eventBytes e).length := by
  intro e he; rw [call0RngEvents_drop_33_eq, List.mem_singleton] at he; subst he
  show 9 < rngDhsBytes.length
  rw [rngDhsBytes_length]
  decide
theorem ptDeadHB_of (hinv : ∀ (r : Records) (S : Sem) (g : Ghost) (ms : List Move), compFitsPinned setup compI0 r → Common443.CompSetupSecrecy.NoBrk r ms → ExplainsMoves compI0 r S who ok g ms (.recv bundleBytes :: call0RngEvents) → IniPrefixStateSecretsInv r S g ms bundleBytes call0RngEvents) : PtDeadHB := by
  intro r S g ms hfits hnb hexp hem hcol; have hwf : RecordsWF r := hfits.1.1; rw [trace_take_35_eq] at hexp hcol; refine not_pt_prefixGhosts_collision_of_ne_bytes hexp.1 ?_ ⟨hem, hcol⟩; intro t ht x hx hinj hval_eq
  have hgt : 9 < x.2.2.length := memoInjGt_prefixTerms_of_matchedPrefix_ini_of hwf hexp.1 (hinv r S g ms hfits hnb hexp)
      (by decide) call0RngEvents_kind call0RngEvents_take_1_gt_9 call0RngEvents_drop_33_gt_9
      t ht x hx hinj
  rw [hval_eq, ptMsg35_length] at hgt; exact Nat.lt_irrefl 9 hgt
theorem not_ptSplitCollisionAt_torsionComp_35_of {r : Records} {S : Sem} {who₀ : List Participant} {ok₀ : Nat → Bool} (hwf : RecordsWF r) (hinv : ∀ (g : Ghost) (ms : List Move), ExplainsMoves compI0 r S who₀ ok₀ g ms (.recv bundleBytes :: call0RngEvents) → IniPrefixStateSecretsInv r S g ms bundleBytes call0RngEvents) : ¬ PtSplitCollisionAt compI0 r S who₀ ok₀ Witnesses.Cheval26SmallSubgroupTorsionComp.trace 35 := by
  refine not_ptSplitCollisionAt_of_ne_bytes torsionComp_trace_getElem?_35 ?_; intro g ms hexp t ht x hx hinj hval_eq; rw [torsionComp_trace_take_35_eq] at hexp
  have hgt : 9 < x.2.2.length := memoInjGt_prefixTerms_of_matchedPrefix_ini_of hwf hexp.1 (hinv g ms hexp)
      (by decide) call0RngEvents_kind call0RngEvents_take_1_gt_9 call0RngEvents_drop_33_gt_9
      t ht x hx hinj
  rw [hval_eq, ptMsg35_length] at hgt; exact Nat.lt_irrefl 9 hgt
theorem iniPrefixStateSecretsInv_call0 {r : Records} {S : Sem} {who₀ : List Participant} {ok₀ : Nat → Bool} {g : Ghost} {ms : List Move} (hwf : RecordsWF r) (hnb : Common443.CompSetupSecrecy.NoBrk r ms) (hexp : ExplainsMoves compI0 r S who₀ ok₀ g ms (.recv bundleBytes :: call0RngEvents)) : IniPrefixStateSecretsInv r S g ms bundleBytes call0RngEvents := Common443.CompPrefixInvIni.iniPrefixStateSecretsInv_of_matchedPrefix_ini hwf hnb hexp.1 call0RngEvents_length call0RngEvents_kind bundleBytes_getElem4_ne_one
theorem ptDead35_self {r : Records} {S : Sem} {who₀ : List Participant} {ok₀ : Nat → Bool}
    {g : Ghost} {ms : List Move} (hwf : RecordsWF r) (hnb : Common443.CompSetupSecrecy.NoBrk r ms)
    (hexp : ExplainsMoves compI0 r S who₀ ok₀ g ms (.recv bundleBytes :: call0RngEvents))
    (hem : EventMatchesEntry compI0 r S g (.pt ptMsg35) (ptEntryOfNextEncrypt r ms)) :
    ¬ MemoCollisionOn compI0 r S g (fun u => u.AttackerKnows (runTraceMoves r ms))
        (runTraceMoves r ms) (runVis r ms)
        (ptEntryOfNextEncrypt r ms).terms (ptEntryOfNextEncrypt r ms).terms := by
  refine not_pt_collision_of_ne_bytes hem fun t ht x hx hinj hval_eq => ?_
  have hgt : 9 < x.2.2.length := memoInjGt_prefixTerms_of_matchedPrefix_ini_of hwf hexp.1
      (iniPrefixStateSecretsInv_call0 hwf hnb hexp)
      (by decide) call0RngEvents_kind call0RngEvents_take_1_gt_9 call0RngEvents_drop_33_gt_9
      t ht x hx hinj
  rw [hval_eq, ptMsg35_length] at hgt; exact Nat.lt_irrefl 9 hgt
theorem ptDeadHB : PtDeadHB :=
  ptDeadHB_of fun _ _ _ _ hfits hnb hexp => iniPrefixStateSecretsInv_call0 hfits.1.1 hnb hexp
theorem not_ptSplitCollisionAt_torsionComp_35 {r : Records} {S : Sem} {who₀ : List Participant} {ok₀ : Nat → Bool} (hwf : RecordsWF r) (hnb : ∀ ms, Common443.CompSetupSecrecy.NoBrk r ms) : ¬ PtSplitCollisionAt compI0 r S who₀ ok₀ Witnesses.Cheval26SmallSubgroupTorsionComp.trace 35 :=
  not_ptSplitCollisionAt_torsionComp_35_of hwf fun _ ms hexp =>
    iniPrefixStateSecretsInv_call0 hwf (hnb ms) hexp
end Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443
