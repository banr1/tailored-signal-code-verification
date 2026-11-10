/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Lits
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import all Init.Data.String.Defs

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

/-!
# Relocatable Read-Only Literals of `main` (`[LibsignalPlacement]`)

Relocatable `[LibsignalPlacement]` counterparts of `Lits.lean`, deriving `mainLitsBlk617` from
`LibsignalRoLoaded lsmpl m` (`mainLitsPlaced_of_roLoaded`, `sepWPp_mainFrame_mainLitsPlaced`).
-/

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj ProofLib CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli

def lsroPrefixCheck (sym : String) (bs : List (BitVec 8)) : Bool :=
  match lsroFind sym with
  | some d =>
    d.readOnly &&
    decide (bs.length ≤ d.bytes.length) &&
    decide (bs.length ≤ 2 ^ 64) &&
    d.relocs.all (fun r =>
      decide (r.off + dataRelocWidth r.kind ≤ d.bytes.length) &&
      decide (bs.length ≤ r.off)) &&
    decide (d.bytes.take bs.length = bs)
  | none => false

theorem lsro_intro_prefix {pl : MultiPlacement} {m : Memory} (hro : LibsignalRoLoaded pl m)
    {sym : String} {bs : List (BitVec 8)} (h : lsroPrefixCheck sym bs = true)
    {P : SepProp} (hP : m ⊨ P) :
    m ⊨ (pl.ρ sym ↦ᵣ bs) ∗ P := by
  unfold lsroPrefixCheck at h
  cases hfind : lsroFind sym with
  | none => simp [hfind] at h
  | some d =>
    simp only [hfind, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hrd, hle⟩, h64⟩, hrel⟩, htake⟩ := h
    obtain ⟨hmem, hsym⟩ := lsroFind_spec hfind
    have hd := hro d hmem hrd
    rw [hsym] at hd
    have hhb : HoldsBytes m (pl.ρ sym) bs (fun _ => Perm.ro) := by
      intro i hi
      have hi_d : i < d.bytes.length := Nat.lt_of_lt_of_le hi hle
      have hget := getElem?_patchedData_of_notReloc (lib := libsignalSessionLib) (pl := pl)
        (d := d) (i := i) (fun r hr => (hrel r hr).1) (fun r hr => Or.inl (Nat.lt_of_lt_of_le hi (hrel r hr).2))
      rw [List.getElem?_append_left hi_d, List.getElem?_eq_getElem hi_d] at hget
      have hi_p : i < (libsignalSessionLib.patchedData pl d).length := by
        by_contra hge
        rw [List.getElem?_eq_none (Nat.le_of_not_lt hge)] at hget
        cases hget
      have hd_i := hd i hi_p
      have hval : (libsignalSessionLib.patchedData pl d)[i]'hi_p = bs[i] := by
        have h1 : some ((libsignalSessionLib.patchedData pl d)[i]'hi_p) = some (d.bytes[i]'hi_d) := by
          rw [← List.getElem?_eq_getElem hi_p]; exact hget
        have h2 : d.bytes[i]'hi_d = bs[i] := by
          have ht : (d.bytes.take bs.length)[i]? = bs[i]? := congrArg (·[i]?) htake
          rw [List.getElem?_take_of_lt hi, List.getElem?_eq_getElem hi_d,
            List.getElem?_eq_getElem hi] at ht
          exact Option.some.inj ht
        exact (Option.some.inj h1).trans h2
      simpa only [hval] using hd_i
    exact Satisfies.of_holdsBytes_ro hhb h64 hP

/-- Block-`617` `.rodata` symbol names and strings for the 7 nonempty `Stores::open()` directory paths. -/
def dirLitsBlk617 : List (String × String) :=
  [("libsignal_cli:.rodata..Lanon.51", "identities"),
   ("libsignal_cli:.rodata..Lanon.46", "signed-pre-keys"),
   ("libsignal_cli:.rodata..Lanon.48", "one-time-kyber-pre-keys"),
   ("libsignal_cli:.rodata..Lanon.49", "last-resort-kyber-pre-keys"),
   ("libsignal_cli:.rodata..Lanon.47", "one-time-pre-keys"),
   ("libsignal_cli:.rodata.cst8+0x0", "sessions"),
   ("libsignal_cli:.rodata..Lanon.53", "public")]

def mainLitsBlk617 [LibsignalPlacement] : SepProp :=
  (lsρ coinsLitSym ↦ᵣ utf8 "coins") ∗
    (dirLitsBlk617.foldr (fun l P => (lsρ l.1 ↦ᵣ utf8 l.2) ∗ P) emp)

private theorem coinsLitSym_chk : lsroPrefixCheck coinsLitSym (utf8 "coins") = true := by
  decide +kernel

private theorem dirLitsBlk617_chk :
    dirLitsBlk617.all (fun l => lsroPrefixCheck l.1 (utf8 l.2)) = true := by
  decide +kernel

private theorem sat_dirLitsBlk617 [LibsignalPlacement] {m : Memory}
    (hro : LibsignalRoLoaded lsmpl m) :
    ∀ {ls : List (String × String)},
      ls.all (fun l => lsroPrefixCheck l.1 (utf8 l.2)) = true →
      ∀ {P : SepProp}, (m ⊨ P) →
        m ⊨ (ls.foldr (fun l Q => (lsρ l.1 ↦ᵣ utf8 l.2) ∗ Q) emp) ∗ P
  | [], _, _, hP => by simpa only [List.foldr_nil, emp_sepConj] using hP
  | l :: ls, hall, _, hP => by
    simp only [List.all_cons, Bool.and_eq_true] at hall
    simp only [List.foldr_cons, sepConj_assoc]
    exact lsro_intro_prefix hro hall.1 (sat_dirLitsBlk617 hro hall.2 hP)

/-- Extracts `mainLitsBlk617` from `LibsignalRoLoaded lsmpl m` alongside any separation-logic frame `P`. -/
theorem mainLitsPlaced_of_roLoaded [LibsignalPlacement] {m : Memory}
    (hro : LibsignalRoLoaded lsmpl m) {P : SepProp} (hP : m ⊨ P) :
    m ⊨ mainLitsBlk617 ∗ P := by
  unfold mainLitsBlk617
  rw [sepConj_assoc]
  exact lsro_intro_prefix hro coinsLitSym_chk (sat_dirLitsBlk617 hro dirLitsBlk617_chk hP)

private theorem foldr_dirLitsBlk617_dup [LibsignalPlacement] :
    ∀ (ls : List (String × String)),
      ((ls.foldr (fun l P => (lsρ l.1 ↦ᵣ utf8 l.2) ∗ P) emp) ∗
        (ls.foldr (fun l P => (lsρ l.1 ↦ᵣ utf8 l.2) ∗ P) emp)) =
        ls.foldr (fun l P => (lsρ l.1 ↦ᵣ utf8 l.2) ∗ P) emp
  | [] => emp_sepConj emp
  | l :: ls => by
    simp only [List.foldr_cons]
    rw [sepConj_assoc, sepConj_left_comm (ls.foldr _ emp), ← sepConj_assoc,
      pointsToBytesRO_dup, foldr_dirLitsBlk617_dup ls]

@[simp] theorem mainLitsBlk617_dup [LibsignalPlacement] :
    (mainLitsBlk617 ∗ mainLitsBlk617) = mainLitsBlk617 := by
  unfold mainLitsBlk617
  rw [sepConj_assoc, sepConj_left_comm (dirLitsBlk617.foldr _ emp), ← sepConj_assoc,
    pointsToBytesRO_dup, foldr_dirLitsBlk617_dup]

/-- Eliminates `mainLitsBlk617` from `mainFrame`'s statics hypothesis under `LibsignalRoLoaded lsmpl s.mem`. -/
theorem sepWPp_mainFrame_mainLitsPlaced [LibsignalPlacement] {prog : Program} {ret : BitVec 64}
    {s : State} {A : RustAlloc} {stk : Nat} {Statics : SepProp} {i : Inputs}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hwp : SepWPp prog ret s (mainFrame A stk (Statics ∗ mainLitsBlk617) i s) Q Qp oom) :
    SepWPp prog ret s (mainFrame A stk Statics i s) Q Qp oom := by
  intro R hm
  apply hwp R
  have h := mainLitsPlaced_of_roLoaded hro hm
  refine Satisfies.of_eq h ?_
  simp only [mainFrame]
  ac_rfl

end CryptoVerification.SignalSession.Cli.MainHops
