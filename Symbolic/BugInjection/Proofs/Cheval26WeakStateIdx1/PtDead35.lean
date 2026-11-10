/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop
public import Symbolic.BugInjection.Proofs.Common443.CompMemoInjGtDraws

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead35
open CryptoProofLib.Refinement (ExternInterpretation)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open Symbolic.BugInjection Symbolic.BugInjection.Proofs.Common443.CompMemoInjGt Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1
attribute [local irreducible] Symbolic.BugInjection.hexBytes
def rngAt (n : Nat) : HwBytes := match ((Witnesses.Cheval26WeakStateIdx1.trace)[n]? : Option MachineEvent) with | some (.rng b) => b | _ => []
def bundle0 : HwBytes := recvAt 0
def call0Rng : List MachineEvent := ((Witnesses.Cheval26WeakStateIdx1.trace).take 35).tail
theorem call0Rng_map_kind : call0Rng.map eventKind = List.replicate 34 .rng := rfl
theorem call0Rng_kind : ∀ e ∈ call0Rng, eventKind e = .rng := fun e he => List.eq_of_mem_replicate (call0Rng_map_kind ▸ List.mem_map.mpr ⟨e, he, rfl⟩)
theorem call0Rng_take_1_eq : call0Rng.take 1 = [.rng (rngAt 1)] := rfl
theorem call0Rng_drop_33_eq : call0Rng.drop 33 = [.rng (rngAt 34)] := rfl
def rng1Chars : List Char := chars_of_hex (rngAt 1)
theorem rngAt1_eq_hex : rngAt 1 = hexBytes (str_of_hex (rngAt 1)) := rfl
theorem rng1Str_eq : (str_of_hex (rngAt 1)) = String.ofList rng1Chars := rfl
theorem rngAt1_length : (rngAt 1).length = 32 := by rw [show rngAt 1 = hexBytes.go hexDigit rng1Chars by rw [rngAt1_eq_hex, rng1Str_eq, hexBytes_ofList]]; rfl
def rng34Chars : List Char := chars_of_hex (rngAt 34)
theorem rngAt34_eq_hex : rngAt 34 = hexBytes (str_of_hex (rngAt 34)) := rfl
theorem rng34Str_eq : (str_of_hex (rngAt 34)) = String.ofList rng34Chars := rfl
theorem rngAt34_length : (rngAt 34).length = 32 := by rw [show rngAt 34 = hexBytes.go hexDigit rng34Chars by rw [rngAt34_eq_hex, rng34Str_eq, hexBytes_ofList]]; rfl
def pt35Chars : List Char := chars_of_hex (ptAt 35)
theorem ptAt35_eq_hex : ptAt 35 = hexBytes (str_of_hex (ptAt 35)) := rfl
theorem pt35Str_eq : (str_of_hex (ptAt 35)) = String.ofList pt35Chars := rfl
theorem ptDeadAt35_of (hinv : ∀ (r : Records) (S : Sem) (g : Ghost) (ms : List Move), compFitsPinned setup compI0 r → Common443.CompSetupSecrecy.NoBrk r ms → ExplainsMoves compI0 r S who ok g ms (.recv bundle0 :: call0Rng) → IniPrefixStateSecretsInv r S g ms bundle0 call0Rng) : PtDeadAt 35 := by
  intro r S g ms hfits hnb hexp hem hcol; rw [show (Witnesses.Cheval26WeakStateIdx1.trace).take 35 = .recv bundle0 :: call0Rng from rfl] at hexp hcol
  refine not_pt_prefixGhosts_collision_of_ne_bytes hexp.1 (fun t ht x hx hinj hval_eq => ?_) ⟨hem, hcol⟩
  have hgt : 5 < x.2.2.length := memoInjGt_prefixTerms_of_matchedPrefix_ini_of hfits.1.1 hexp.1 (hinv r S g ms hfits hnb hexp) (by decide) call0Rng_kind
    (by intro e he; rw [call0Rng_take_1_eq, List.mem_singleton] at he; subst he; show 5 < (rngAt 1).length; rw [rngAt1_length]; decide)
    (by intro e he; rw [call0Rng_drop_33_eq, List.mem_singleton] at he; subst he; show 5 < (rngAt 34).length; rw [rngAt34_length]; decide) t ht x hx hinj
  have hlen : (ptAt 35).length = 5 := by rw [show ptAt 35 = hexBytes.go hexDigit pt35Chars by rw [ptAt35_eq_hex, pt35Str_eq, hexBytes_ofList]]; rfl
  rw [hval_eq, hlen] at hgt; exact Nat.lt_irrefl 5 hgt
theorem ptDeadAt35_self_of (hinv : ∀ (r : Records) (S : Sem) (g : Ghost) (ms : List Move), compFitsPinned setup compI0 r → Common443.CompSetupSecrecy.NoBrk r ms → ExplainsMoves compI0 r S who ok g ms (.recv bundle0 :: call0Rng) → IniPrefixStateSecretsInv r S g ms bundle0 call0Rng)
    (r : Records) (S : Sem) (g : Ghost) (ms : List Move) (hfits : compFitsPinned setup compI0 r)
    (hnb : Common443.CompSetupSecrecy.NoBrk r ms)
    (hexp : ExplainsMoves compI0 r S who ok g ms ((Witnesses.Cheval26WeakStateIdx1.trace).take 35))
    (hem : EventMatchesEntry compI0 r S g (.pt (ptAt 35)) (ptEntryOfNextEncrypt r ms)) :
    ¬ MemoCollisionOn compI0 r S g (fun u => u.AttackerKnows (runTraceMoves r ms))
        (runTraceMoves r ms) (runVis r ms)
        (ptEntryOfNextEncrypt r ms).terms (ptEntryOfNextEncrypt r ms).terms := by
  rw [show (Witnesses.Cheval26WeakStateIdx1.trace).take 35 = .recv bundle0 :: call0Rng from rfl] at hexp
  refine not_pt_collision_of_ne_bytes hem fun t ht x hx hinj hval_eq => ?_
  have hgt : 5 < x.2.2.length := memoInjGt_prefixTerms_of_matchedPrefix_ini_of hfits.1.1 hexp.1 (hinv r S g ms hfits hnb hexp) (by decide) call0Rng_kind
    (by intro e he; rw [call0Rng_take_1_eq, List.mem_singleton] at he; subst he; show 5 < (rngAt 1).length; rw [rngAt1_length]; decide)
    (by intro e he; rw [call0Rng_drop_33_eq, List.mem_singleton] at he; subst he; show 5 < (rngAt 34).length; rw [rngAt34_length]; decide) t ht x hx hinj
  have hlen : (ptAt 35).length = 5 := by rw [show ptAt 35 = hexBytes.go hexDigit pt35Chars by rw [ptAt35_eq_hex, pt35Str_eq, hexBytes_ofList]]; rfl
  rw [hval_eq, hlen] at hgt; exact Nat.lt_irrefl 5 hgt
end Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead35
