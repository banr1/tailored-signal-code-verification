/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.StdCli.Layout
public import CaseStudies.Hashbrown.Proofs.InternalTop
public import ProofLib.AsciiNum

/-!
# Pure Parser, Line-Scanner, and Allocator Budget Lemmas

Pure lemmas for `hashbrown` CLI command parsing (`parseCommand`, `parseDecimalU64`), line splitting
(`splitLines`, `evalLinesStep`), and `hbStdLimits` insert and resize allocator budgets.
-/

set_option autoImplicit false

@[expose] public section

/-! ## `Map64` and `CliMap` Bridges -/

namespace CaseStudies.Hashbrown.Proofs

open CaseStudies.Hashbrown

def Map64.lookup (m : Map64) (k : BitVec 64) : Option (BitVec 64) := cliMapLookup k m

def Map64.erase (m : Map64) (k : BitVec 64) : Map64 := cliMapErase k m

def Map64.insert (m : Map64) (k v : BitVec 64) : Map64 := cliMapInsert k v m

@[simp] theorem Map64.lookup_eq_cliMapLookup (m : Map64) (k : BitVec 64) :
    m.lookup k = cliMapLookup k m := rfl

@[simp] theorem Map64.erase_eq_cliMapErase (m : Map64) (k : BitVec 64) :
    m.erase k = cliMapErase k m := rfl

@[simp] theorem Map64.insert_eq_cliMapInsert (m : Map64) (k v : BitVec 64) :
    m.insert k v = cliMapInsert k v m := rfl

@[simp] theorem listLookup_eq_cliMapLookup (m : Map64) (k : BitVec 64) :
    List.lookup k m = cliMapLookup k m := by
  induction m with
  | nil => rfl
  | cons kv rest ih =>
    rcases kv with ⟨k', v'⟩; simp only [List.lookup, cliMapLookup]
    by_cases h : k == k'
    · cases beq_iff_eq.mp h; simp
    · have hne : k ≠ k' := fun heq => h (beq_iff_eq.mpr heq)
      simp [beq_eq_false_iff_ne.mpr (Ne.symm hne), Bool.eq_false_iff.mpr h, ih]

end CaseStudies.Hashbrown.Proofs

namespace CaseStudies.Hashbrown.Proofs.StdCli

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.StdStartup
open CaseStudies.Hashbrown CaseStudies.Hashbrown.Proofs

/-! ## `splitLines` and `splitOnByte` Scanner Lemmas -/

@[simp] theorem splitLines_nil : splitLines [] = [] := rfl

theorem splitLines_of_pos {bs : List (BitVec 8)} (h : 0 < bs.length) :
    splitLines bs = splitOnByte 0x0a#8
      (bs.take (if bs[bs.length - 1]'(by omega) = 0x0a#8 then bs.length - 1 else bs.length)) := by
  have hne : bs ≠ [] := List.ne_nil_of_length_pos h
  have hlast : bs.getLast? = some (bs[bs.length - 1]'(by omega)) := by
    rw [List.getLast?_eq_some_getLast hne, List.getLast_eq_getElem]
  unfold splitLines; rw [List.isEmpty_eq_false_iff.mpr hne]
  simp only [Bool.false_eq_true, ↓reduceIte, hlast]
  by_cases heq : (bs[bs.length - 1]'(by omega)) = 0x0a#8
  · simp [heq, List.dropLast_eq_take]
  · have hbeq : ((some (bs[bs.length - 1]'(by omega)) : Option (BitVec 8)) == some 0x0a#8) = false :=
      beq_eq_false_iff_ne.mpr fun hs => heq (Option.some.inj hs)
    simp [heq, hbeq, List.take_length]

@[simp] theorem splitOnByte_nil (sep : BitVec 8) : splitOnByte sep [] = [[]] := rfl

theorem splitOnByte_ne_nil (sep : BitVec 8) (bs : List (BitVec 8)) :
    splitOnByte sep bs ≠ [] := by
  cases bs with
  | nil => simp [splitOnByte]
  | cons b rest => simp only [splitOnByte]; split <;> (try split) <;> simp

theorem splitOnByte_of_first_eq {sep : BitVec 8} {bs : List (BitVec 8)} {k : Nat}
    (hk : k < bs.length) (heq : bs[k] = sep)
    (hprev : ∀ j (hj : j < k), bs[j]'(by omega) ≠ sep) :
    splitOnByte sep bs = bs.take k :: splitOnByte sep (bs.drop (k + 1)) := by
  induction k generalizing bs with
  | zero =>
    cases bs with
    | nil => simp at hk
    | cons b rest => simp only [List.getElem_cons_zero] at heq; subst heq; simp [splitOnByte]
  | succ k ih =>
    cases bs with
    | nil => simp at hk
    | cons b rest =>
      have hb_beq : (b == sep) = false :=
        beq_eq_false_iff_ne.mpr (by simpa using hprev 0 (Nat.zero_lt_succ k))
      have hk_rest : k < rest.length := Nat.lt_of_succ_lt_succ (by simpa using hk)
      simp [splitOnByte, hb_beq, ih hk_rest (by simpa using heq)
        (fun j hj => by simpa using hprev (j + 1) (Nat.succ_lt_succ hj))]

private theorem splitOnByte_eq_singleton_of_forall_ne {sep : BitVec 8} {bs : List (BitVec 8)}
    (hall : ∀ j (hj : j < bs.length), bs[j] ≠ sep) : splitOnByte sep bs = [bs] := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    have hb_beq : (b == sep) = false :=
      beq_eq_false_iff_ne.mpr (by simpa using hall 0 (Nat.zero_lt_succ rest.length))
    simp [splitOnByte, hb_beq, ih (fun j hj => by simpa using hall (j + 1) (Nat.succ_lt_succ hj))]

theorem splitOnByte_of_forall_ne {sep : BitVec 8} {bs : List (BitVec 8)}
    (_hne : bs ≠ []) (hall : ∀ j (hj : j < bs.length), bs[j] ≠ sep) :
    splitOnByte sep bs = [bs] := splitOnByte_eq_singleton_of_forall_ne hall

def evalLinesStep :
    (CliMap × List (BitVec 8) × List (BitVec 8)) → List (BitVec 8) →
      CliMap × List (BitVec 8) × List (BitVec 8) :=
  fun ((m, o, e) : CliMap × List (BitVec 8) × List (BitVec 8)) line =>
    match parseCommand line with
    | none                   => (m, o, e ++ bytesOfString "error: invalid command\n")
    | some (.insert k v)     => (cliMapInsert k v m, o, e)
    | some (.remove k)       => (cliMapErase k m, o, e)
    | some (.get k)          => (m, o ++ formatGetResult (cliMapLookup k m), e)
    | some (.contains k)     => (m, o ++ formatBoolResult (cliMapLookup k m).isSome, e)
    | some (.withCapacity _) => ([], o, e)
    | some .len              => (m, o ++ formatDecimalNat m.length ++ bytesOfString "\n", e)
    | some .isEmpty          => (m, o ++ formatBoolResult m.isEmpty, e)
    | some .clear            => ([], o, e)

theorem evalLines_eq_foldl (lines : List (List (BitVec 8))) :
    evalLines lines = let (_, o, e) := lines.foldl evalLinesStep ([], [], []); (o, e) := rfl

@[simp] theorem formatBoolResult_true : formatBoolResult true = trueNlBytes := rfl
@[simp] theorem formatBoolResult_false : formatBoolResult false = falseNlBytes := rfl

theorem formatBoolResult_eq_ite (b : Bool) :
    formatBoolResult b = if b then trueNlBytes else falseNlBytes := by
  cases b <;> rfl

@[simp] theorem formatGetResult_none : formatGetResult none = noneNlBytes := rfl
@[simp] theorem formatGetResult_some (v : BitVec 64) :
    formatGetResult (some v) = formatDecimalNat v.toNat ++ bytesOfString "\n" := rfl

@[simp] theorem cliMap_isEmpty_iff (m : CliMap) :
    m.isEmpty = decide (m.length = 0) := by
  cases m <;> rfl

@[simp] theorem evalLinesStep_of_parseCommand_none (m : CliMap) (o e line : List (BitVec 8))
    (h : parseCommand line = none) :
    evalLinesStep (m, o, e) line = (m, o, e ++ errInvalidCmdBytes) := by
  simp [evalLinesStep, h, errInvalidCmdBytes]

@[simp] theorem evalLinesStep_of_parseCommand_insert (m : CliMap) (o e line : List (BitVec 8))
    (k v : BitVec 64) (h : parseCommand line = some (.insert k v)) :
    evalLinesStep (m, o, e) line = (cliMapInsert k v m, o, e) := by
  simp [evalLinesStep, h]

@[simp] theorem evalLinesStep_of_parseCommand_remove (m : CliMap) (o e line : List (BitVec 8))
    (k : BitVec 64) (h : parseCommand line = some (.remove k)) :
    evalLinesStep (m, o, e) line = (cliMapErase k m, o, e) := by
  simp [evalLinesStep, h]

@[simp] theorem evalLinesStep_of_parseCommand_get (m : CliMap) (o e line : List (BitVec 8))
    (k : BitVec 64) (h : parseCommand line = some (.get k)) :
    evalLinesStep (m, o, e) line = (m, o ++ formatGetResult (cliMapLookup k m), e) := by
  simp [evalLinesStep, h]

@[simp] theorem evalLinesStep_of_parseCommand_contains (m : CliMap) (o e line : List (BitVec 8))
    (k : BitVec 64) (h : parseCommand line = some (.contains k)) :
    evalLinesStep (m, o, e) line = (m, o ++ formatBoolResult (cliMapLookup k m).isSome, e) := by
  simp [evalLinesStep, h]

@[simp] theorem evalLinesStep_of_parseCommand_withCapacity (m : CliMap) (o e line : List (BitVec 8))
    (cap : BitVec 64) (h : parseCommand line = some (.withCapacity cap)) :
    evalLinesStep (m, o, e) line = ([], o, e) := by
  simp [evalLinesStep, h]

@[simp] theorem evalLinesStep_of_parseCommand_len (m : CliMap) (o e line : List (BitVec 8))
    (h : parseCommand line = some .len) :
    evalLinesStep (m, o, e) line = (m, o ++ formatDecimalNat m.length ++ bytesOfString "\n", e) := by
  simp [evalLinesStep, h]

@[simp] theorem evalLinesStep_of_parseCommand_isEmpty (m : CliMap) (o e line : List (BitVec 8))
    (h : parseCommand line = some .isEmpty) :
    evalLinesStep (m, o, e) line = (m, o ++ formatBoolResult m.isEmpty, e) := by
  simp [evalLinesStep, h]

@[simp] theorem evalLinesStep_of_parseCommand_clear (m : CliMap) (o e line : List (BitVec 8))
    (h : parseCommand line = some .clear) :
    evalLinesStep (m, o, e) line = ([], o, e) := by
  simp [evalLinesStep, h]

/-! ## Prefix Word-Load, `splitFirstByte`, and `parseDecimalU64` Lemmas -/

def packU32le (b0 b1 b2 b3 : BitVec 8) : BitVec 32 := b3 ++ b2 ++ b1 ++ b0

@[simp] theorem packU32le_eq_pack32 (b0 b1 b2 b3 : BitVec 8) :
    packU32le b0 b1 b2 b3 = pack32 b0 b1 b2 b3 := rfl

theorem packU32le_eq_iff (b0 b1 b2 b3 c0 c1 c2 c3 : BitVec 8) :
    packU32le b0 b1 b2 b3 = packU32le c0 c1 c2 c3 ↔
      b0 = c0 ∧ b1 = c1 ∧ b2 = c2 ∧ b3 = c3 := by
  refine ⟨fun h => ?_, ?_⟩
  · have hu := congrArg unpack32 h; unfold packU32le at hu
    rw [unpack32_pack32, unpack32_pack32] at hu; simpa only [List.cons.injEq, and_true] using hu
  · rintro ⟨rfl, rfl, rfl, rfl⟩; rfl

theorem getPrefixConst_add :
    (0x20746567#32 : BitVec 32) + 0xcfe#32 = 0x20747265#32 := by decide

theorem stripBytePrefix_eq_if (pfx bs : List (BitVec 8)) :
    stripBytePrefix pfx bs =
      if pfx.length ≤ bs.length ∧ bs.take pfx.length = pfx then some (bs.drop pfx.length)
      else none := by
  induction pfx generalizing bs with
  | nil => simp [stripBytePrefix]
  | cons p ps ih =>
    cases bs with
    | nil => simp [stripBytePrefix]
    | cons b rest =>
      simp only [stripBytePrefix, List.length_cons, List.take_succ_cons, List.drop_succ_cons]
      by_cases hpb : p = b
      · subst hpb; simp [ih rest]
      · simp [beq_eq_false_iff_ne.mpr hpb, Ne.symm hpb]

theorem stripBytePrefix_eq_none_of_length_lt {pfx bs : List (BitVec 8)}
    (h : bs.length < pfx.length) : stripBytePrefix pfx bs = none := by
  rw [stripBytePrefix_eq_if]; simp [Nat.not_le_of_lt h]

theorem stripBytePrefix_eq_some_iff {pfx bs rest : List (BitVec 8)} :
    stripBytePrefix pfx bs = some rest ↔ bs = pfx ++ rest := by
  rw [stripBytePrefix_eq_if]; refine ⟨fun h => ?_, ?_⟩
  · split at h
    · rename_i hc; cases h; have htd := List.take_append_drop pfx.length bs
      rw [hc.2] at htd; exact htd.symm
    · cases h
  · rintro rfl; simp

private theorem stripBytePrefix_eq_none_of_not_some {pfx line : List (BitVec 8)}
    (h : stripBytePrefix pfx line ≠ some (line.drop pfx.length)) :
    stripBytePrefix pfx line = none := by
  by_cases hc : pfx.length ≤ line.length ∧ line.take pfx.length = pfx <;>
    simp [stripBytePrefix_eq_if, hc] at h ⊢

theorem stripBytePrefix_eq_none_of_lt {pfx bs : List (BitVec 8)}
    (h : bs.length < pfx.length) : stripBytePrefix pfx bs = none :=
  stripBytePrefix_eq_none_of_length_lt h

theorem stripBytePrefix_eq_some_of_take_eq {pfx bs : List (BitVec 8)}
    (hle : pfx.length ≤ bs.length) (heq : bs.take pfx.length = pfx) :
    stripBytePrefix pfx bs = some (bs.drop pfx.length) := by
  simp [stripBytePrefix_eq_if, hle, heq]

theorem stripBytePrefix_eq_none_of_take_ne {pfx bs : List (BitVec 8)}
    (hne : bs.take pfx.length ≠ pfx) :
    stripBytePrefix pfx bs = none := by
  simp [stripBytePrefix_eq_if, hne]

theorem stripBytePrefix_eq_none_of_ne {pfx bs : List (BitVec 8)}
    (h : bs.length < pfx.length ∨ bs.take pfx.length ≠ pfx) :
    stripBytePrefix pfx bs = none := by
  rcases h with hlt | hne
  · exact stripBytePrefix_eq_none_of_length_lt hlt
  · exact stripBytePrefix_eq_none_of_take_ne hne

theorem stripBytePrefix_of_le {pfx bs : List (BitVec 8)} (hle : pfx.length ≤ bs.length) :
    stripBytePrefix pfx bs =
      if (bs.take pfx.length == pfx) then some (bs.drop pfx.length) else none := by
  rw [stripBytePrefix_eq_if]
  by_cases heq : bs.take pfx.length = pfx
  · simp [hle, heq]
  · simp [hle, heq, beq_eq_false_iff_ne.mpr heq]

theorem bytes_beq_eq_true_iff (line pat : List (BitVec 8)) :
    (line == pat) = true ↔ line = pat :=
  beq_iff_eq

theorem bytes_beq_false_of_length_ne {line pat : List (BitVec 8)}
    (h : line.length ≠ pat.length) :
    (line == pat) = false :=
  beq_eq_false_iff_ne.mpr (fun heq => h (congrArg List.length heq))

theorem bytes_beq_cons_eq {x y : BitVec 8} (xs ys : List (BitVec 8)) (h : x = y) :
    ((x :: xs) == (y :: ys)) = (xs == ys) := by
  subst h; simp

theorem bytes_beq_cons_ne {x y : BitVec 8} (xs ys : List (BitVec 8)) (h : x ≠ y) :
    ((x :: xs) == (y :: ys)) = false :=
  beq_eq_false_iff_ne.mpr (fun heq => h (List.cons.inj heq).1)

theorem bytes_beq_eq_false_iff (line pat : List (BitVec 8)) :
    (line == pat) = false ↔
      (line.length ≠ pat.length ∨
       ∃ i < line.length, (∀ j < i, line[j]? = pat[j]?) ∧ line[i]? ≠ pat[i]?) := by
  rw [beq_eq_false_iff_ne]
  induction line generalizing pat with
  | nil =>
    cases pat with
    | nil => simp
    | cons _ _ => simp
  | cons x xs ih =>
    cases pat with
    | nil => simp
    | cons y ys =>
      by_cases hxy : x = y
      · subst hxy
        have hcons : (x :: xs ≠ x :: ys) ↔ xs ≠ ys := by simp
        have hlen : (x :: xs).length ≠ (x :: ys).length ↔ xs.length ≠ ys.length := by simp
        rw [hcons, ih ys, hlen]
        refine or_congr Iff.rfl ⟨?_, ?_⟩
        · rintro ⟨i, hi, hprev, hne⟩
          refine ⟨i + 1, Nat.succ_lt_succ hi, fun j hj => ?_, by simpa using hne⟩
          rcases j with _ | j
          · rfl
          · simpa using hprev j (Nat.lt_of_succ_lt_succ hj)
        · rintro ⟨k, hk, hprev, hne⟩
          rcases k with _ | i
          · simp at hne
          · refine ⟨i, Nat.lt_of_succ_lt_succ hk, fun j hj => ?_, by simpa using hne⟩
            simpa using hprev (j + 1) (Nat.succ_lt_succ hj)
      · refine ⟨fun _ => Or.inr ⟨0, Nat.zero_lt_succ _, fun j hj => by omega, by simp [hxy]⟩,
                fun _ hcons => hxy (List.cons.inj hcons).1⟩

private theorem bytesOfString_get : bytesOfString "get " = [0x67#8, 0x65#8, 0x74#8, 0x20#8] := by decide
private theorem bytesOfString_insert :
    bytesOfString "insert " = [0x69#8, 0x6e#8, 0x73#8, 0x65#8, 0x72#8, 0x74#8, 0x20#8] := by decide
private theorem bytesOfString_remove :
    bytesOfString "remove " = [0x72#8, 0x65#8, 0x6d#8, 0x6f#8, 0x76#8, 0x65#8, 0x20#8] := by decide

private theorem take_four_of_ge_four {bs : List (BitVec 8)} (h : 4 ≤ bs.length) :
    bs.take 4 = [bs[0]'(by omega), bs[1]'(by omega), bs[2]'(by omega), bs[3]'(by omega)] := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, rest⟩⟩⟩⟩ <;> simp at h ⊢

private theorem take_seven_of_ge_seven {bs : List (BitVec 8)} (h : 7 ≤ bs.length) :
    bs.take 7 = [bs[0]'(by omega), bs[1]'(by omega), bs[2]'(by omega), bs[3]'(by omega),
                 bs[4]'(by omega), bs[5]'(by omega), bs[6]'(by omega)] := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, rest⟩⟩⟩⟩⟩⟩⟩ <;> simp at h ⊢

theorem stripBytePrefix_get_of_lt_four {line : List (BitVec 8)} (h : line.length < 4) :
    stripBytePrefix (bytesOfString "get ") line = none :=
  stripBytePrefix_eq_none_of_length_lt (by simpa [bytesOfString_get] using h)
theorem stripBytePrefix_insert_of_lt_seven {line : List (BitVec 8)} (h : line.length < 7) :
    stripBytePrefix (bytesOfString "insert ") line = none :=
  stripBytePrefix_eq_none_of_length_lt (by simpa [bytesOfString_insert] using h)
theorem stripBytePrefix_remove_of_lt_seven {line : List (BitVec 8)} (h : line.length < 7) :
    stripBytePrefix (bytesOfString "remove ") line = none :=
  stripBytePrefix_eq_none_of_length_lt (by simpa [bytesOfString_remove] using h)
theorem stripBytePrefix_contains_of_lt_nine {line : List (BitVec 8)} (h : line.length < 9) :
    stripBytePrefix pfxContainsBytes line = none :=
  stripBytePrefix_eq_none_of_length_lt (by simpa [pfxContainsBytes_length] using h)
theorem stripBytePrefix_withCap_of_lt_fourteen {line : List (BitVec 8)} (h : line.length < 14) :
    stripBytePrefix pfxWithCapBytes line = none :=
  stripBytePrefix_eq_none_of_length_lt (by simpa [pfxWithCapBytes_length] using h)

theorem packU32le_eq_get_iff {line : List (BitVec 8)} (h4 : 4 ≤ line.length) :
    packU32le (line[0]'(by omega)) (line[1]'(by omega)) (line[2]'(by omega)) (line[3]'(by omega)) =
      0x20746567#32 ↔ stripBytePrefix (bytesOfString "get ") line = some (line.drop 4) := by
  rw [show (0x20746567#32 : BitVec 32) = packU32le 0x67#8 0x65#8 0x74#8 0x20#8 by decide,
      packU32le_eq_iff, stripBytePrefix_eq_if, bytesOfString_get]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, h4, true_and, take_four_of_ge_four h4]
  refine ⟨fun ⟨h0, h1, h2, h3⟩ => by simp [h0, h1, h2, h3], fun hs => ?_⟩
  split at hs
  · rename_i heq; simpa only [List.cons.injEq, and_true] using heq
  · cases hs

theorem stripBytePrefix_get_eq_none_of_packU32le_ne {line : List (BitVec 8)} (h4 : 4 ≤ line.length)
    (hne : packU32le (line[0]'(by omega)) (line[1]'(by omega)) (line[2]'(by omega)) (line[3]'(by omega)) ≠
      0x20746567#32) : stripBytePrefix (bytesOfString "get ") line = none :=
  stripBytePrefix_eq_none_of_not_some fun hs => hne ((packU32le_eq_get_iff h4).mpr hs)

private theorem packU32le_seven_iff {line : List (BitVec 8)} (h7 : 7 ≤ line.length)
    (c0 c1 c2 c3 c4 c5 c6 : BitVec 8) :
    (packU32le (line[0]'(by omega)) (line[1]'(by omega)) (line[2]'(by omega)) (line[3]'(by omega)) = packU32le c0 c1 c2 c3 ∧
     packU32le (line[3]'(by omega)) (line[4]'(by omega)) (line[5]'(by omega)) (line[6]'(by omega)) = packU32le c3 c4 c5 c6) ↔
      stripBytePrefix [c0, c1, c2, c3, c4, c5, c6] line = some (line.drop 7) := by
  rw [packU32le_eq_iff, packU32le_eq_iff, stripBytePrefix_eq_if]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, h7, true_and, take_seven_of_ge_seven h7]
  refine ⟨fun ⟨⟨h0, h1, h2, h3⟩, ⟨_, h4, h5, h6⟩⟩ => by simp [h0, h1, h2, h3, h4, h5, h6], fun hs => ?_⟩
  split at hs
  · rename_i heq; simp only [List.cons.injEq, and_true] at heq
    rcases heq with ⟨h0, h1, h2, h3, h4, h5, h6⟩; exact ⟨⟨h0, h1, h2, h3⟩, ⟨h3, h4, h5, h6⟩⟩
  · cases hs

theorem packU32le_eq_insert_iff {line : List (BitVec 8)} (h7 : 7 ≤ line.length) :
    (packU32le (line[0]'(by omega)) (line[1]'(by omega)) (line[2]'(by omega)) (line[3]'(by omega)) = 0x65736e69#32 ∧
     packU32le (line[3]'(by omega)) (line[4]'(by omega)) (line[5]'(by omega)) (line[6]'(by omega)) = 0x20747265#32) ↔
      stripBytePrefix (bytesOfString "insert ") line = some (line.drop 7) := by
  rw [bytesOfString_insert]; exact packU32le_seven_iff h7 0x69#8 0x6e#8 0x73#8 0x65#8 0x72#8 0x74#8 0x20#8

theorem stripBytePrefix_insert_eq_none_of_ne {line : List (BitVec 8)} (h7 : 7 ≤ line.length)
    (hne : ¬ (packU32le (line[0]'(by omega)) (line[1]'(by omega)) (line[2]'(by omega)) (line[3]'(by omega)) = 0x65736e69#32 ∧
              packU32le (line[3]'(by omega)) (line[4]'(by omega)) (line[5]'(by omega)) (line[6]'(by omega)) = 0x20747265#32)) :
    stripBytePrefix (bytesOfString "insert ") line = none :=
  stripBytePrefix_eq_none_of_not_some fun hs => hne ((packU32le_eq_insert_iff h7).mpr hs)

theorem packU32le_eq_remove_iff {line : List (BitVec 8)} (h7 : 7 ≤ line.length) :
    (packU32le (line[0]'(by omega)) (line[1]'(by omega)) (line[2]'(by omega)) (line[3]'(by omega)) = 0x6f6d6572#32 ∧
     packU32le (line[3]'(by omega)) (line[4]'(by omega)) (line[5]'(by omega)) (line[6]'(by omega)) = 0x2065766f#32) ↔
      stripBytePrefix (bytesOfString "remove ") line = some (line.drop 7) := by
  rw [bytesOfString_remove]
  exact packU32le_seven_iff h7 0x72#8 0x65#8 0x6d#8 0x6f#8 0x76#8 0x65#8 0x20#8

theorem stripBytePrefix_remove_eq_none_of_ne {line : List (BitVec 8)} (h7 : 7 ≤ line.length)
    (hne : ¬ (packU32le (line[0]'(by omega)) (line[1]'(by omega)) (line[2]'(by omega)) (line[3]'(by omega)) = 0x6f6d6572#32 ∧
              packU32le (line[3]'(by omega)) (line[4]'(by omega)) (line[5]'(by omega)) (line[6]'(by omega)) = 0x2065766f#32)) :
    stripBytePrefix (bytesOfString "remove ") line = none :=
  stripBytePrefix_eq_none_of_not_some fun hs => hne ((packU32le_eq_remove_iff h7).mpr hs)

theorem withCap_le_max_iff (cap : BitVec 64) :
    cap ≤ 0x1000#64 ↔ cap.toNat ≤ MaxWithCapacity := Iff.rfl

theorem withCap_gt_max_iff (cap : BitVec 64) :
    0x1000#64 < cap ↔ ¬ (cap.toNat ≤ MaxWithCapacity) := by
  rw [BitVec.lt_def, show (0x1000#64).toNat = MaxWithCapacity from rfl]; omega

theorem parseCommand_of_insert_pfx {line rest : List (BitVec 8)}
    (h : stripBytePrefix pfxInsertBytes line = some rest) :
    parseCommand line =
      match splitFirstByte 0x20#8 rest with
      | some (ks, vs) => do
        let k ← parseDecimalU64 ks
        let v ← parseDecimalU64 vs
        some (.insert k v)
      | none => none := by
  unfold parseCommand pfxInsertBytes at *; simp [h]
  cases splitFirstByte 0x20#8 rest with
  | none => rfl
  | some p => obtain ⟨ks, vs⟩ := p; cases parseDecimalU64 ks <;> cases parseDecimalU64 vs <;> rfl

theorem parseCommand_of_remove_pfx {line rest : List (BitVec 8)}
    (h1 : stripBytePrefix pfxInsertBytes line = none)
    (h2 : stripBytePrefix pfxRemoveBytes line = some rest) :
    parseCommand line = (parseDecimalU64 rest).map .remove := by
  unfold parseCommand pfxInsertBytes pfxRemoveBytes at *
  simp [h1, h2]; cases parseDecimalU64 rest <;> rfl

theorem parseCommand_of_get_pfx {line rest : List (BitVec 8)}
    (h1 : stripBytePrefix pfxInsertBytes line = none)
    (h2 : stripBytePrefix pfxRemoveBytes line = none)
    (h3 : stripBytePrefix pfxGetBytes line = some rest) :
    parseCommand line = (parseDecimalU64 rest).map .get := by
  unfold parseCommand pfxInsertBytes pfxRemoveBytes pfxGetBytes at *
  simp [h1, h2, h3]; cases parseDecimalU64 rest <;> rfl

theorem parseCommand_of_contains_pfx {line rest : List (BitVec 8)}
    (h1 : stripBytePrefix pfxInsertBytes line = none)
    (h2 : stripBytePrefix pfxRemoveBytes line = none)
    (h3 : stripBytePrefix pfxGetBytes line = none)
    (h4 : stripBytePrefix pfxContainsBytes line = some rest) :
    parseCommand line = (parseDecimalU64 rest).map .contains := by
  unfold parseCommand pfxInsertBytes pfxRemoveBytes pfxGetBytes pfxContainsBytes at *
  simp [h1, h2, h3, h4]; cases parseDecimalU64 rest <;> rfl

theorem parseCommand_of_withCap_pfx {line rest : List (BitVec 8)}
    (h1 : stripBytePrefix pfxInsertBytes line = none)
    (h2 : stripBytePrefix pfxRemoveBytes line = none)
    (h3 : stripBytePrefix pfxGetBytes line = none)
    (h4 : stripBytePrefix pfxContainsBytes line = none)
    (h5 : stripBytePrefix pfxWithCapBytes line = some rest) :
    parseCommand line = (do
      let cap ← parseDecimalU64 rest
      if cap.toNat ≤ MaxWithCapacity then some (.withCapacity cap) else none) := by
  unfold parseCommand pfxInsertBytes pfxRemoveBytes pfxGetBytes pfxContainsBytes pfxWithCapBytes at *
  simp [h1, h2, h3, h4, h5]
  cases parseDecimalU64 rest with
  | none => rfl
  | some c => by_cases hc : c.toNat ≤ MaxWithCapacity <;> simp [hc, «guard», failure] <;> rfl

theorem parseCommand_of_no_pfx {line : List (BitVec 8)}
    (h1 : stripBytePrefix pfxInsertBytes line = none)
    (h2 : stripBytePrefix pfxRemoveBytes line = none)
    (h3 : stripBytePrefix pfxGetBytes line = none)
    (h4 : stripBytePrefix pfxContainsBytes line = none)
    (h5 : stripBytePrefix pfxWithCapBytes line = none) :
    parseCommand line =
      if line == cmdLenBytes then some .len
      else if line == cmdIsEmptyBytes then some .isEmpty
      else if line == cmdClearBytes then some .clear
      else none := by
  unfold parseCommand pfxInsertBytes pfxRemoveBytes pfxGetBytes pfxContainsBytes pfxWithCapBytes
    cmdLenBytes cmdIsEmptyBytes cmdClearBytes at *
  simp [h1, h2, h3, h4, h5]

theorem parseCommand_of_lt_three {line : List (BitVec 8)} (h : line.length < 3) :
    parseCommand line = none := by
  have h1 := stripBytePrefix_insert_of_lt_seven (by omega : line.length < 7)
  have h2 := stripBytePrefix_remove_of_lt_seven (by omega : line.length < 7)
  have h3 := stripBytePrefix_get_of_lt_four (by omega : line.length < 4)
  have h4 := stripBytePrefix_contains_of_lt_nine (by omega : line.length < 9)
  have h5 := stripBytePrefix_withCap_of_lt_fourteen (by omega : line.length < 14)
  rw [parseCommand_of_no_pfx h1 h2 h3 h4 h5,
      bytes_beq_false_of_length_ne (by simpa [cmdLenBytes_length] using Nat.ne_of_lt h),
      bytes_beq_false_of_length_ne (by simpa [cmdIsEmptyBytes_length] using by omega),
      bytes_beq_false_of_length_ne (by simpa [cmdClearBytes_length] using by omega)]
  rfl

@[simp] theorem splitFirstByte_nil (sep : BitVec 8) : splitFirstByte sep [] = none := rfl

theorem splitFirstByte_of_first_eq {sep : BitVec 8} {rest : List (BitVec 8)} {k : Nat}
    (hk : k < rest.length) (heq : rest[k] = sep)
    (hprev : ∀ j (hj : j < k), rest[j]'(by omega) ≠ sep) :
    splitFirstByte sep rest = some (rest.take k, rest.drop (k + 1)) := by
  induction k generalizing rest with
  | zero =>
    cases rest with
    | nil => simp at hk
    | cons b tail => simp only [List.getElem_cons_zero] at heq; subst heq; simp [splitFirstByte]
  | succ k ih =>
    cases rest with
    | nil => simp at hk
    | cons b tail =>
      have hb_beq : (b == sep) = false :=
        beq_eq_false_iff_ne.mpr (by simpa using hprev 0 (Nat.zero_lt_succ k))
      have hk_tail : k < tail.length := Nat.lt_of_succ_lt_succ (by simpa using hk)
      simp [splitFirstByte, hb_beq, ih hk_tail (by simpa using heq)
        (fun j hj => by simpa using hprev (j + 1) (Nat.succ_lt_succ hj))]

theorem splitFirstByte_of_forall_ne {sep : BitVec 8} {rest : List (BitVec 8)}
    (hall : ∀ j (hj : j < rest.length), rest[j] ≠ sep) : splitFirstByte sep rest = none := by
  induction rest with
  | nil => rfl
  | cons b tail ih =>
    have hb_beq : (b == sep) = false :=
      beq_eq_false_iff_ne.mpr (by simpa using hall 0 (Nat.zero_lt_succ tail.length))
    simp [splitFirstByte, hb_beq, ih (fun j hj => by simpa using hall (j + 1) (Nat.succ_lt_succ hj))]

theorem splitFirstByte_eq_some_append {sep : BitVec 8} {rest ks vs : List (BitVec 8)}
    (h : splitFirstByte sep rest = some (ks, vs)) : rest = ks ++ sep :: vs := by
  induction rest generalizing ks with
  | nil => simp [splitFirstByte] at h
  | cons b tail ih =>
    simp only [splitFirstByte] at h
    by_cases hb : b == sep
    · simp only [hb, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩; rw [beq_iff_eq.mp hb]; rfl
    · simp only [hb, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at h
      rcases h with ⟨⟨lhs, rhs⟩, hsub, heq⟩; cases heq; simp [ih hsub]

def parseDecimalFold (acc : Nat) (bs : List (BitVec 8)) : Option Nat :=
  bs.foldlM (init := acc) fun a b =>
    if 0x30#8 ≤ b && b ≤ 0x39#8 then
      let next := a * 10 + (b.toNat - 0x30)
      if next < 2 ^ 64 then some next else none
    else none

theorem parseDecimalU64_eq_fold (bs : List (BitVec 8)) :
    parseDecimalU64 bs =
      if bs.isEmpty then none else (parseDecimalFold 0 bs).map (BitVec.ofNat 64) :=
  ProofLib.AsciiNum.parseDecimalU64_eq_boundedFold bs

@[simp] theorem parseDecimalU64_nil : parseDecimalU64 [] = none := rfl

theorem parseDecimalU64_of_nonempty {bs : List (BitVec 8)} (hne : bs ≠ []) :
    parseDecimalU64 bs = (parseDecimalFold 0 bs).map (BitVec.ofNat 64) := by
  rw [parseDecimalU64_eq_fold, List.isEmpty_eq_false_iff.mpr hne]; rfl

@[simp] theorem parseDecimalFold_nil (acc : Nat) : parseDecimalFold acc [] = some acc := rfl

theorem digitSub_le_nine_iff (b : BitVec 8) :
    (b.zeroExtend 32 - 0x30#32) ≤ 9#32 ↔ (0x30#8 ≤ b && b ≤ 0x39#8) = true := by
  have hb_lt : b.toNat < 256 := b.isLt
  have hsub : (b.zeroExtend 32 - 0x30#32).toNat = (b.toNat + 2 ^ 32 - 48) % 2 ^ 32 := by
    rw [BitVec.toNat_sub, BitVec.toNat_setWidth]
    change (2 ^ 32 - 48 + b.toNat % 2 ^ 32) % 2 ^ 32 = (b.toNat + 2 ^ 32 - 48) % 2 ^ 32; omega
  rw [BitVec.le_def, hsub]
  change (b.toNat + 2 ^ 32 - 48) % 2 ^ 32 ≤ 9 ↔
    (decide (48 ≤ b.toNat) && decide (b.toNat ≤ 57)) = true
  simp only [Bool.and_eq_true, decide_eq_true_eq]; omega

private theorem digitSub32_toNat {b : BitVec 8} (h : (0x30#8 ≤ b && b ≤ 0x39#8) = true) :
    (b.zeroExtend 32 - 0x30#32).toNat = b.toNat - 48 ∧ b.toNat ≤ 57 := by
  have hb : 48 ≤ b.toNat ∧ b.toNat ≤ 57 := by
    change (decide (48 ≤ b.toNat) && decide (b.toNat ≤ 57)) = true at h
    simpa [Bool.and_eq_true, decide_eq_true_eq] using h
  refine ⟨?_, hb.2⟩; rw [BitVec.toNat_sub, BitVec.toNat_setWidth]
  change (2 ^ 32 - 48 + b.toNat % 2 ^ 32) % 2 ^ 32 = b.toNat - 48; omega

theorem digitSub_toNat_of_le_nine {b : BitVec 8} (h : (0x30#8 ≤ b && b ≤ 0x39#8) = true) :
    ((b.zeroExtend 32 - 0x30#32).zeroExtend 64).toNat = b.toNat - 0x30 := by
  obtain ⟨hs, hle⟩ := digitSub32_toNat h
  rw [BitVec.toNat_setWidth, hs, Nat.mod_eq_of_lt (by omega)]

theorem digitSub_uxtb_toNat_of_le_nine {b : BitVec 8} (h : (0x30#8 ≤ b && b ≤ 0x39#8) = true) :
    (((b.zeroExtend 32 - 0x30#32).truncate 8).zeroExtend 64).toNat = b.toNat - 0x30 := by
  obtain ⟨hs, hle⟩ := digitSub32_toNat h
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, hs,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem mulTen_shift_eq (acc : BitVec 64) : ((acc + (acc <<< 2)) <<< 1) = acc * 10#64 := by bv_lin

theorem mulTen_add_lt_pow64_iff (acc d : BitVec 64) :
    acc.toNat * 10 + d.toNat < 2 ^ 64 ↔
      (acc.toNat * 10) / 2 ^ 64 = 0 ∧ (acc * 10#64).toNat + d.toNat < 2 ^ 64 := by
  have hm : (acc * 10#64).toNat = (acc.toNat * 10) % 2 ^ 64 := by rw [BitVec.toNat_mul]; rfl
  rw [hm]; omega

theorem mulTen_add_toNat {acc d : BitVec 64} (h : acc.toNat * 10 + d.toNat < 2 ^ 64) :
    (acc * 10#64 + d).toNat = acc.toNat * 10 + d.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_mul]
  change ((acc.toNat * 10) % 2 ^ 64 + d.toNat) % 2 ^ 64 = acc.toNat * 10 + d.toNat; omega

theorem umulh_ten_eq_zero_iff (acc : BitVec 64) :
    (((acc.zeroExtend 128 * (10#64).zeroExtend 128) >>> 64).truncate 64 = 0#64) ↔
      (acc.toNat * 10) / 2 ^ 64 = 0 := by
  have hacc : acc.toNat < 2 ^ 64 := acc.isLt
  have hprod : (acc.zeroExtend 128 * (10#64).zeroExtend 128).toNat = acc.toNat * 10 := by
    rw [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_setWidth]
    change ((acc.toNat % 2 ^ 128) * (10 % 2 ^ 128)) % 2 ^ 128 = acc.toNat * 10; omega
  refine ⟨fun hz => ?_, fun hdiv => BitVec.eq_of_toNat_eq ?_⟩
  · have htn := congrArg BitVec.toNat hz
    rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, hprod, Nat.shiftRight_eq_div_pow] at htn
    change ((acc.toNat * 10) / 2 ^ 64) % 2 ^ 64 = 0 at htn; omega
  · rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, hprod, Nat.shiftRight_eq_div_pow, hdiv]; rfl

theorem parseDecimalFold_cons_invalid (acc : Nat) {b : BitVec 8} (rest : List (BitVec 8))
    (h : ¬ (0x30#8 ≤ b && b ≤ 0x39#8) = true) : parseDecimalFold acc (b :: rest) = none := by
  unfold parseDecimalFold; rw [List.foldlM_cons, Bool.eq_false_iff.mpr h]; rfl

theorem parseDecimalFold_cons_valid_ok {acc d : BitVec 64} {b : BitVec 8} (rest : List (BitVec 8))
    (hb : (0x30#8 ≤ b && b ≤ 0x39#8) = true) (hd : d.toNat = b.toNat - 0x30)
    (hok : (acc.toNat * 10) / 2 ^ 64 = 0 ∧ (acc * 10#64).toNat + d.toNat < 2 ^ 64) :
    parseDecimalFold acc.toNat (b :: rest) = parseDecimalFold (acc * 10#64 + d).toNat rest := by
  have hlt0 := (mulTen_add_lt_pow64_iff acc d).mpr hok
  have hlt : acc.toNat * 10 + (b.toNat - 0x30) < 2 ^ 64 := by rwa [← hd]
  have hnext : (acc * 10#64 + d).toNat = acc.toNat * 10 + (b.toNat - 0x30) := by
    rw [← hd]; exact mulTen_add_toNat hlt0
  unfold parseDecimalFold; rw [List.foldlM_cons, hb]; simp [hlt, hnext]

theorem parseDecimalFold_cons_valid_overflow {acc d : BitVec 64} {b : BitVec 8} (rest : List (BitVec 8))
    (hb : (0x30#8 ≤ b && b ≤ 0x39#8) = true) (hd : d.toNat = b.toNat - 0x30)
    (hovf : ¬ ((acc.toNat * 10) / 2 ^ 64 = 0 ∧ (acc * 10#64).toNat + d.toNat < 2 ^ 64)) :
    parseDecimalFold acc.toNat (b :: rest) = none := by
  have hnlt : ¬ (acc.toNat * 10 + (b.toNat - 0x30) < 2 ^ 64) := by
    rw [← hd]; exact fun hlt => hovf ((mulTen_add_lt_pow64_iff acc d).mp hlt)
  unfold parseDecimalFold; rw [List.foldlM_cons, hb]; simp [hnlt]

/-! ## Insert-Count and `hbStdLimits` Allocator Budget Lemmas -/

def isInsertLine (line : List (BitVec 8)) : Bool :=
  match parseCommand line with | some (.insert _ _) => true | _ => false

theorem insertLine_length_ge_ten {line : List (BitVec 8)} (h : isInsertLine line = true) :
    10 ≤ line.length := by
  unfold isInsertLine parseCommand at h
  cases hins : stripBytePrefix (bytesOfString "insert ") line with
  | none =>
    simp only [hins] at h
    cases hrem : stripBytePrefix (bytesOfString "remove ") line with
    | some r => cases hp : parseDecimalU64 r <;> simp [hrem, hp] at h
    | none =>
      simp only [hrem] at h
      cases hget : stripBytePrefix (bytesOfString "get ") line with
      | some r => cases hp : parseDecimalU64 r <;> simp [hget, hp] at h
      | none =>
        simp only [hget] at h
        cases hcon : stripBytePrefix (bytesOfString "contains ") line with
        | some r => cases hp : parseDecimalU64 r <;> simp [hcon, hp] at h
        | none =>
          simp only [hcon] at h
          cases hwcap : stripBytePrefix (bytesOfString "with_capacity ") line with
          | some r =>
            simp only [hwcap] at h
            cases hcap : parseDecimalU64 r with
            | none => simp [hcap] at h
            | some cap =>
              by_cases hc : cap.toNat ≤ MaxWithCapacity <;>
                simp [hcap, «guard», failure, hc] at h
          | none =>
            simp only [hwcap] at h
            by_cases h1 : line == bytesOfString "len" <;>
              by_cases h2 : line == bytesOfString "is_empty" <;>
                by_cases h3 : line == bytesOfString "clear" <;>
                  simp [h1, h2, h3] at h
  | some rest =>
    simp only [hins] at h
    have hline_eq := stripBytePrefix_eq_some_iff.mp hins
    cases hsp : splitFirstByte 0x20#8 rest with
    | none => simp [hsp] at h
    | some kv =>
      rcases kv with ⟨ks, vs⟩; simp only [hsp] at h
      have hrest_eq := splitFirstByte_eq_some_append hsp
      have hks : 1 ≤ ks.length := by cases ks with | nil => simp at h | cons _ _ => simp
      have hvs : 1 ≤ vs.length := by
        cases vs with
        | nil => cases parseDecimalU64 ks <;> simp at h
        | cons _ _ => simp
      have hpfx : (bytesOfString "insert ").length = 7 := by decide
      rw [hline_eq, hrest_eq, List.length_append, List.length_append, List.length_cons, hpfx]; omega

theorem splitOnByte_length_sum (sep : BitVec 8) (bs : List (BitVec 8)) :
    ((splitOnByte sep bs).map List.length).sum + (splitOnByte sep bs).length = bs.length + 1 := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    simp only [splitOnByte]
    by_cases hb : b == sep
    · simp only [hb, ↓reduceIte, List.map_cons, List.length_nil, List.sum_cons, List.length_cons]; omega
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      rcases hsp : splitOnByte sep rest with _ | ⟨l, ls⟩
      · exact False.elim (splitOnByte_ne_nil sep rest hsp)
      · rw [hsp] at ih; simp only [List.map_cons, List.sum_cons, List.length_cons] at ih ⊢; omega

private theorem lines_insertCount_bound (ls : List (List (BitVec 8))) :
    11 * (ls.filter isInsertLine).length ≤ (ls.map List.length).sum + ls.length := by
  induction ls with
  | nil => simp
  | cons l rest ih =>
    simp only [List.filter_cons, List.map_cons, List.sum_cons, List.length_cons]
    by_cases hl : isInsertLine l = true
    · have := insertLine_length_ge_ten hl; simp only [hl, ↓reduceIte, List.length_cons]; omega
    · simp only [Bool.eq_false_iff.mpr hl, Bool.false_eq_true, ↓reduceIte]; omega

theorem splitOnByte_insertCount_bound {core : List (BitVec 8)}
    {doneLines remLines : List (List (BitVec 8))} {curLine : List (BitVec 8)}
    (hsplit : splitOnByte 0x0a#8 core = doneLines ++ curLine :: remLines)
    (hcur : isInsertLine curLine = true) :
    11 * ((doneLines.filter isInsertLine).length + 1) ≤ core.length + 1 := by
  have hsum := splitOnByte_length_sum 0x0a#8 core
  have hbound := lines_insertCount_bound (splitOnByte 0x0a#8 core)
  have hfilt : (doneLines.filter isInsertLine).length + 1 ≤
      ((splitOnByte 0x0a#8 core).filter isInsertLine).length := by
    rw [hsplit, List.filter_append, List.length_append, List.filter_cons, hcur]
    simp only [↓reduceIte, List.length_cons]; omega
  omega

theorem cliMapErase_length_le (k : BitVec 64) (m : CliMap) :
    (cliMapErase k m).length ≤ m.length := by
  induction m with
  | nil => simp
  | cons kv rest ih =>
    rcases kv with ⟨k', v'⟩; simp only [cliMapErase, List.length_cons]
    by_cases hk : k' == k
    · simp only [hk, ↓reduceIte]; omega
    · simp only [hk, Bool.false_eq_true, ↓reduceIte, List.length_cons]; omega

theorem cliMapInsert_length_le_succ (k v : BitVec 64) (m : CliMap) :
    (cliMapInsert k v m).length ≤ m.length + 1 := by
  unfold cliMapInsert; simp only [List.length_cons]; have := cliMapErase_length_le k m; omega

theorem evalLinesStep_mapLength_step (st : CliMap × List (BitVec 8) × List (BitVec 8))
    (line : List (BitVec 8)) :
    (evalLinesStep st line).1.length ≤ st.1.length + (if isInsertLine line then 1 else 0) := by
  rcases st with ⟨m, o, e⟩; unfold evalLinesStep isInsertLine
  cases hcmd : parseCommand line with
  | none => simp
  | some cmd =>
    cases cmd with
    | insert k v => simp only [↓reduceIte]; exact cliMapInsert_length_le_succ k v m
    | remove k => have := cliMapErase_length_le k m; simp only [Bool.false_eq_true, ↓reduceIte]; omega
    | get k => simp
    | contains k => simp
    | withCapacity cap => simp
    | len => simp
    | isEmpty => simp
    | clear => simp

theorem evalLinesStep_foldl_mapLength_le (lines : List (List (BitVec 8)))
    (st : CliMap × List (BitVec 8) × List (BitVec 8)) :
    (lines.foldl evalLinesStep st).1.length ≤ st.1.length + (lines.filter isInsertLine).length := by
  induction lines generalizing st with
  | nil => simp
  | cons line rest ih =>
    simp only [List.foldl_cons, List.filter_cons]
    have hstep := evalLinesStep_mapLength_step st line
    have hih := ih (evalLinesStep st line)
    by_cases hl : isInsertLine line = true
    · simp only [hl, ↓reduceIte, List.length_cons] at hstep ⊢; omega
    · simp only [Bool.eq_false_iff.mpr hl, Bool.false_eq_true, ↓reduceIte] at hstep ⊢; omega

theorem evalLinesStep_mapLength_le_insertCount (lines : List (List (BitVec 8))) :
    (lines.foldl evalLinesStep ([], [], [])).1.length ≤ (lines.filter isInsertLine).length := by
  simpa using evalLinesStep_foldl_mapLength_le lines ([], [], [])

private theorem max_le_add_right (a b : Nat) : max a b ≤ a + b :=
  Nat.max_le.mpr ⟨Nat.le_add_right a b, Nat.le_add_left b a⟩

private theorem hbCli_reserve_arith {L vecCap lc B : Nat}
    (hB : 77 * B ≤ 8 * L + 308) (hvec : vecCap ≤ 2 * L + 32)
    (hlc : lc ≤ 65536 + 65536 + (if vecCap = 0 then 0 else max vecCap 65536) + (17 * B + 8 + 65536)) :
    8 ≤ 34 * B + 8 ∧ 34 * B + 8 ≤ (272 * L) / 77 + 139272 ∧
    lc + max (34 * B + 8) 65536 ≤ (562 * L) / 77 + 336000 := by
  have hv : (if vecCap = 0 then 0 else max vecCap 65536) ≤ 2 * L + 65536 := by split <;> omega
  have hn : max (34 * B + 8) 65536 ≤ 34 * B + 8 + 65536 := max_le_add_right _ _
  exact ⟨by omega, by omega, by omega⟩

theorem hbCli_canInsertOne {P : Program} {addrs : MallocngAddrs} {L : Nat}
    (M : MallocngCoreIface P addrs (hbStdLimits L)) (γ : GhostName) (CodeInv : Memory → Prop)
    (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    {m : Map64} {bm : BitVec 64} {k_ins vecCap lc blk B : Nat}
    (hL : L ≤ HashbrownCliMaxStdin) (hins : 11 * (k_ins + 1) ≤ L + 1) (hlen : m.length ≤ k_ins)
    (hbm_wf : bm = 0#64 ∨ ValidBucketMask bm) (_hbm_bound : bm ≠ 0#64 → bm.toNat + 1 ≤ B)
    (hvec : vecCap ≤ 2 * L + 32)
    (hlc : lc ≤ mallocngBlockCost 8192 + mallocngBlockCost 1024 +
                (if vecCap = 0 then 0 else mallocngBlockCost vecCap) +
                hbMapCost (HbAlloc.ofMallocng M γ CodeInv hCodeInv) bm)
    (hblk : blk ≤ 4) :
    HbCanInsertOne (HbAlloc.ofMallocng M γ CodeInv hCodeInv) m bm k_ins lc blk := by
  by_cases hfast : k_ins < bucketMaskToCapacity bm
  · exact Or.inl hfast
  · right; right
    have h8192 : mallocngBlockCost 8192 = 65536 := by decide
    have h1024 : mallocngBlockCost 1024 = 65536 := by decide
    have hblk' : blk + 1 ≤ 5 := by clear P addrs M γ CodeInv hCodeInv hlc; omega
    rcases hbm_wf with rfl | hv
    · refine ⟨by decide, ?_⟩
      rw [h8192, h1024, hbMapCost_zero] at hlc
      rw [show tableAllocBytes (nextResizeMask 0#64) = 76 by decide]
      dsimp only [HbAlloc.ofMallocng, hbStdLimits]
      rw [show mallocngBlockCost 76 = 65536 by decide]
      refine ⟨by decide, by decide, by decide, ?_, ?_, hblk'⟩
      · clear P addrs M γ CodeInv hCodeInv hlc; omega
      · clear P addrs M γ CodeInv hCodeInv; unfold mallocngBlockCost MallocngMinBlockCost at hlc
        have hv0 : (if vecCap = 0 then 0 else max vecCap 65536) ≤ 2 * L + 65536 := by split <;> omega
        omega
    · have hbm_ne : bm ≠ 0#64 := ValidBucketMask.ne_zero hv
      have hcap_lt_max : bucketMaskToCapacity bm < MaxHashbrownCapacity := by
        have : HashbrownCliMaxStdin = 10 * 2 ^ 30 := rfl; have : MaxHashbrownCapacity = 7 * 2 ^ 55 := rfl
        clear P addrs M γ CodeInv hCodeInv hlc _hbm_bound; omega
      obtain ⟨hv_next, hnext_bkt⟩ := ValidBucketMask.nextResizeMask_valid hv hcap_lt_max
      have hsz_eq : tableAllocBytes (nextResizeMask bm) = 34 * (bm.toNat + 1) + 8 := by
        have hnext_ne := ValidBucketMask.ne_zero hv_next; clear P addrs M γ CodeInv hCodeInv hlc
        unfold tableAllocBytes; simp only [hnext_ne, ↓reduceIte, hnext_bkt]; omega
      have hmap_le : hbMapCost (HbAlloc.ofMallocng M γ CodeInv hCodeInv) bm ≤ 17 * (bm.toNat + 1) + 8 + 65536 := by
        unfold hbMapCost tableAllocBytes HbAlloc.ofMallocng mallocngBlockCost MallocngMinBlockCost
        simp only [hbm_ne, ↓reduceIte]; exact max_le_add_right _ _
      have hB : 77 * (bm.toNat + 1) ≤ 8 * L + 308 := by
        obtain ⟨exp, hge2, hle58, hbm_eq⟩ := hv
        have hbkt := ValidBucketMask.buckets_eq hge2 hle58 hbm_eq
        have hcap := ValidBucketMask.capacity_eq hge2 hle58 hbm_eq
        clear P addrs M γ CodeInv hCodeInv hlc hmap_le hv_next hnext_bkt hsz_eq hcap_lt_max _hbm_bound
        by_cases he2 : exp = 2
        · subst he2; simp at hbkt; omega
        · have hbkt3 : bm.toNat + 1 = 8 * 2 ^ (exp - 3) := by
            rw [hbkt]; conv => lhs; rw [show exp = (exp - 3) + 3 by omega]
            rw [Nat.pow_add]; omega
          simp only [he2, ↓reduceIte] at hcap; omega
      have hlc' : lc ≤ 65536 + 65536 + (if vecCap = 0 then 0 else max vecCap 65536) + (17 * (bm.toNat + 1) + 8 + 65536) := by
        rw [h8192, h1024] at hlc; exact Nat.le_trans hlc (Nat.add_le_add_left hmap_le _)
      obtain ⟨hc1, hc2, hc3⟩ := hbCli_reserve_arith hB hvec hlc'
      refine ⟨hcap_lt_max, ?_⟩; rw [hsz_eq]
      dsimp only [HbAlloc.ofMallocng, hbStdLimits, mallocngBlockCost, MallocngMinBlockCost]
      exact ⟨by decide, by decide, hc1, hc2, hc3, hblk'⟩

theorem capToBucketMask_valid_of_ne_zero {cap : BitVec 64}
    (h0 : cap ≠ 0#64) (hle : cap.toNat ≤ MaxWithCapacity) :
    ValidBucketMask (capToBucketMask cap.toNat) ∧
    (capToBucketMask cap.toNat).toNat + 1 ≤ 8192 := by
  have hmax : MaxWithCapacity = 4096 := rfl
  have hz : cap.toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq h)
  by_cases h4 : cap.toNat < 4
  · have hbm : capToBucketMask cap.toNat = 3#64 := by simp [capToBucketMask, hz, h4]
    exact ⟨⟨2, by decide, by decide, hbm⟩, by rw [hbm]; decide⟩
  · by_cases h8 : cap.toNat < 8
    · have hbm : capToBucketMask cap.toNat = 7#64 := by simp [capToBucketMask, hz, h4, h8]
      exact ⟨⟨3, by decide, by decide, hbm⟩, by rw [hbm]; decide⟩
    · by_cases h15 : cap.toNat < 15
      · have hbm : capToBucketMask cap.toNat = 15#64 := by simp [capToBucketMask, hz, h4, h8, h15]
        exact ⟨⟨4, by decide, by decide, hbm⟩, by rw [hbm]; decide⟩
      · let adj := (cap.toNat * 8) / 7
        let exp := Nat.log2 (adj - 1) + 1
        have hadj_ne : adj - 1 ≠ 0 := by omega
        have hexp_ge : 2 ≤ exp := by
          have := (Nat.le_log2 hadj_ne).mpr (by omega : 2 ^ 4 ≤ adj - 1)
          omega
        have hexp_le13 : exp ≤ 13 := by
          have := (Nat.log2_lt hadj_ne).mpr (by omega : adj - 1 < 2 ^ 13)
          omega
        have hbm : capToBucketMask cap.toNat = BitVec.ofNat 64 (2 ^ exp - 1) := by
          simp [capToBucketMask, hz, h4, h8, h15, adj, exp]
        have hv : ValidBucketMask (capToBucketMask cap.toNat) := ⟨exp, hexp_ge, by omega, hbm⟩
        have hbkt : (capToBucketMask cap.toNat).toNat + 1 ≤ 8192 := by
          rw [ValidBucketMask.buckets_eq hexp_ge (by omega) hbm]
          exact Nat.le_trans (Nat.pow_le_pow_right (by decide : 0 < 2) hexp_le13) (by decide)
        exact ⟨hv, hbkt⟩

theorem capToBucketMask_wf_of_le_maxWithCap {cap : BitVec 64} (hle : cap.toNat ≤ MaxWithCapacity) :
    let bm := capToBucketMask cap.toNat
    (bm = 0#64 ∨ ValidBucketMask bm) ∧
    bm.toNat + 1 ≤ 8192 ∧
    (∀ k_ins : Nat, bm ≠ 0#64 → bm.toNat + 1 ≤ max 8192 (3 * k_ins)) := by
  by_cases h0 : cap = 0#64
  · subst h0; simp [capToBucketMask]
  · obtain ⟨hv, hbkt⟩ := capToBucketMask_valid_of_ne_zero h0 hle
    exact ⟨Or.inr hv, hbkt, fun k_ins _ => Nat.le_trans hbkt (Nat.le_max_left _ _)⟩

private theorem hbCli_withCap_arith {L vecCap lc B : Nat}
    (hB : B ≤ 8192) (hvec : vecCap ≤ 2 * L + 32)
    (hlc : lc ≤ 65536 + 65536 + (if vecCap = 0 then 0 else max vecCap 65536)) :
    8 ≤ 17 * B + 8 ∧ 17 * B + 8 ≤ (272 * L) / 77 + 139272 ∧
    lc + max (17 * B + 8) 65536 ≤ (562 * L) / 77 + 336000 := by
  have hv : (if vecCap = 0 then 0 else max vecCap 65536) ≤ 2 * L + 65536 := by split <;> omega
  have hn : max (17 * B + 8) 65536 ≤ 139272 := by omega
  exact ⟨by omega, by omega, by omega⟩

theorem hbCli_canWithCapacity {P : Program} {addrs : MallocngAddrs} {L : Nat}
    (M : MallocngCoreIface P addrs (hbStdLimits L)) (γ : GhostName) (CodeInv : Memory → Prop)
    (hCodeInv : ∀ {m1 m2 : Memory}, m1.KeepsFrozen m2 → CodeInv m1 → CodeInv m2)
    {cap : BitVec 64} {vecCap lc blk : Nat}
    (hcap : cap.toNat ≤ MaxWithCapacity)
    (hvec : vecCap ≤ 2 * L + 32)
    (hlc : lc ≤ mallocngBlockCost 8192 + mallocngBlockCost 1024 +
                (if vecCap = 0 then 0 else mallocngBlockCost vecCap))
    (hblk : blk ≤ 4) :
    HbCanWithCapacity (HbAlloc.ofMallocng M γ CodeInv hCodeInv) cap lc blk := by
  have hmax : MaxWithCapacity = 4096 := rfl
  have hmaxH : MaxHashbrownCapacity = 7 * 2 ^ 55 := rfl
  refine ⟨by omega, ?_⟩
  by_cases h0 : cap = 0#64
  · exact Or.inl h0
  · right
    obtain ⟨hv, hbkt_le⟩ := capToBucketMask_valid_of_ne_zero h0 hcap
    have hbm_ne : capToBucketMask cap.toNat ≠ 0#64 := ValidBucketMask.ne_zero hv
    have hsz_eq : tableAllocBytes (capToBucketMask cap.toNat) =
        17 * ((capToBucketMask cap.toNat).toNat + 1) + 8 := by
      unfold tableAllocBytes; simp [hbm_ne]
    have h8192 : mallocngBlockCost 8192 = 65536 := by decide
    have h1024 : mallocngBlockCost 1024 = 65536 := by decide
    have hblk' : blk + 1 ≤ 5 := by clear P addrs M γ CodeInv hCodeInv hlc; omega
    have hlc' : lc ≤ 65536 + 65536 + (if vecCap = 0 then 0 else max vecCap 65536) := by
      rw [h8192, h1024] at hlc
      exact hlc
    obtain ⟨hc1, hc2, hc3⟩ := hbCli_withCap_arith hbkt_le hvec hlc'
    rw [hsz_eq]
    dsimp only [HbAlloc.ofMallocng, hbStdLimits, mallocngBlockCost, MallocngMinBlockCost]
    exact ⟨by decide, by decide, hc1, hc2, hc3, hblk'⟩

theorem hbCli_vecGrow_budget {cap L : Nat}
    (_h1 : 1 ≤ cap) (hcap : cap ≤ L) (_hL : L ≤ HashbrownCliMaxStdin) :
    let newCap := max (cap + 32) (2 * cap)
    newCap ≤ 2 * L + 32 ∧ newCap ≤ (hbStdLimits L).maxReq ∧
    ∀ lc, lc ≤ mallocngBlockCost 8192 + mallocngBlockCost 1024 + mallocngBlockCost cap →
      lc + mallocngBlockCost newCap ≤ (hbStdLimits L).maxPeakCost := by
  dsimp only [hbStdLimits, mallocngBlockCost, MallocngMinBlockCost]
  exact ⟨by omega, by omega, fun lc hlc => by omega⟩

end CaseStudies.Hashbrown.Proofs.StdCli
