/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Spec.CoreFromUtf8

/-!
# Structural Properties and Conformance Checks for `runUtf8Validation`

Proves ASCII-prefix stepping (`runUtf8ValidationLoop_ascii_cons`,
`runUtf8ValidationLoop_ascii_append`) and `Utf8Error.valid_up_to` bounds for `runUtf8Validation`
(`VerifiedLibraries.RustStd.Spec.CoreFromUtf8`), together with RFC 3629 / Unicode Table 3-7
conformance checks.
-/

@[expose] public section

set_option autoImplicit false

namespace VerifiedLibraries.RustStd

open Arm64

/-! ## Derived Predicates and Decidable Equality -/

def isValidUtf8 (bs : List (BitVec 8)) : Bool :=
  match runUtf8Validation bs with
  | .ok () => true
  | .error _ => false

instance instDecidableEqExceptUtf8ErrorUnit : DecidableEq (Except Utf8Error Unit)
  | .ok (), .ok () => isTrue rfl
  | .ok (), .error _ => isFalse (by intro h; cases h)
  | .error _, .ok () => isFalse (by intro h; cases h)
  | .error e1, .error e2 =>
    if h : e1 = e2 then isTrue (h ▸ rfl)
    else isFalse (fun heq => h (Except.error.inj heq))

/-! ## Structural Step Lemmas -/

@[simp]
theorem runUtf8ValidationLoop_nil (offset : Nat) :
    runUtf8ValidationLoop offset [] = .ok () := rfl

theorem runUtf8ValidationLoop_ascii_cons {offset : Nat} {b : BitVec 8} {rest : List (BitVec 8)}
    (hb : b < 0x80#8) :
    runUtf8ValidationLoop offset (b :: rest) = runUtf8ValidationLoop (offset + 1) rest := by
  conv => lhs; unfold runUtf8ValidationLoop
  exact ite_eq_left_iff.mpr (fun h => False.elim (h hb))

theorem runUtf8ValidationLoop_ascii_append {available : List (BitVec 8)} :
    ∀ (pfx : List (BitVec 8)) (offset : Nat),
      (∀ b ∈ pfx, b < 0x80#8) →
      runUtf8ValidationLoop offset (pfx ++ available) =
        runUtf8ValidationLoop (offset + pfx.length) available
  | [], _, _ => rfl
  | b :: ps, offset, hall => by
    have hb : b < 0x80#8 := hall b (List.mem_cons_self ..)
    have hps : ∀ x ∈ ps, x < 0x80#8 := fun x hx => hall x (List.mem_cons_of_mem b hx)
    rw [List.cons_append, runUtf8ValidationLoop_ascii_cons hb,
      runUtf8ValidationLoop_ascii_append ps (offset + 1) hps]
    simp only [List.length_cons]
    have heq : offset + 1 + ps.length = offset + (ps.length + 1) := by omega
    rw [heq]

theorem runUtf8ValidationLoop_valid_up_to_lt :
    ∀ (rem : List (BitVec 8)) (offset : Nat) {err : Utf8Error},
      runUtf8ValidationLoop offset rem = .error err →
      offset ≤ err.valid_up_to ∧ err.valid_up_to < offset + rem.length
  | [], _, _, h => by cases h
  | b0 :: rest, offset, err, h => by
    unfold runUtf8ValidationLoop at h
    by_cases h0 : b0 < 0x80#8
    · simp only [h0, ↓reduceIte] at h
      have ih := runUtf8ValidationLoop_valid_up_to_lt rest (offset + 1) h
      simp only [List.length_cons]; omega
    · simp only [h0, ↓reduceIte] at h
      by_cases h2 : (0xc2#8 ≤ b0 && b0 ≤ 0xdf#8) = true
      · simp only [h2, ↓reduceIte] at h
        cases rest with
        | nil => injection h with he; subst he; simp
        | cons b1 rest1 =>
          dsimp only at h
          cases hc1 : isUtf8ContByte b1 <;> simp only [hc1, Bool.false_eq_true, ↓reduceIte] at h
          · injection h with he; subst he; simp
          · have ih := runUtf8ValidationLoop_valid_up_to_lt rest1 (offset + 2) h
            simp only [List.length_cons]; omega
      · simp only [h2] at h
        by_cases h3 : (0xe0#8 ≤ b0 && b0 ≤ 0xef#8) = true
        · simp only [h3, ↓reduceIte] at h
          cases rest with
          | nil => injection h with he; subst he; simp
          | cons b1 rest1 =>
            dsimp only at h
            let ok2 : Bool :=
              if b0 == 0xe0#8 then 0xa0#8 ≤ b1 && b1 ≤ 0xbf#8
              else if b0 == 0xed#8 then 0x80#8 ≤ b1 && b1 ≤ 0x9f#8
              else isUtf8ContByte b1
            change (if (!ok2) = true then _ else _) = _ at h
            cases hok2 : ok2 <;> simp only [hok2, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
            · injection h with he; subst he; simp
            · cases rest1 with
              | nil => injection h with he; subst he; simp
              | cons b2 rest2 =>
                dsimp only at h
                cases hc2 : isUtf8ContByte b2 <;> simp only [hc2, Bool.false_eq_true, ↓reduceIte] at h
                · injection h with he; subst he; simp
                · have ih := runUtf8ValidationLoop_valid_up_to_lt rest2 (offset + 3) h
                  simp only [List.length_cons]; omega
        · simp only [h3] at h
          by_cases h4 : (0xf0#8 ≤ b0 && b0 ≤ 0xf4#8) = true
          · simp only [h4, ↓reduceIte] at h
            cases rest with
            | nil => injection h with he; subst he; simp
            | cons b1 rest1 =>
              dsimp only at h
              let ok2 : Bool :=
                if b0 == 0xf0#8 then 0x90#8 ≤ b1 && b1 ≤ 0xbf#8
                else if b0 == 0xf4#8 then 0x80#8 ≤ b1 && b1 ≤ 0x8f#8
                else isUtf8ContByte b1
              change (if (!ok2) = true then _ else _) = _ at h
              cases hok2 : ok2 <;> simp only [hok2, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
              · injection h with he; subst he; simp
              · cases rest1 with
                | nil => injection h with he; subst he; simp
                | cons b2 rest2 =>
                  dsimp only at h
                  cases hc2 : isUtf8ContByte b2 <;>
                    simp only [hc2, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
                  · injection h with he; subst he; simp
                  · cases rest2 with
                    | nil => injection h with he; subst he; simp
                    | cons b3 rest3 =>
                      dsimp only at h
                      cases hc3 : isUtf8ContByte b3 <;>
                        simp only [hc3, Bool.false_eq_true, ↓reduceIte] at h
                      · injection h with he; subst he; simp
                      · have ih := runUtf8ValidationLoop_valid_up_to_lt rest3 (offset + 4) h
                        simp only [List.length_cons]; omega
          · simp only [h4] at h
            injection h with he; subst he; simp

theorem runUtf8Validation_valid_up_to_lt {bs : List (BitVec 8)} {err : Utf8Error}
    (h : runUtf8Validation bs = .error err) :
    err.valid_up_to < bs.length := by
  have := (runUtf8ValidationLoop_valid_up_to_lt bs 0 h).2
  omega

/-! ## Edge-Case Conformance Checks -/

section Examples

-- Empty slice `""` -> `Ok ()`
example : runUtf8Validation [] = .ok () := rfl

-- Pure ASCII `"hello"` -> `Ok ()`
example : runUtf8Validation [0x68#8, 0x65#8, 0x6c#8, 0x6c#8, 0x6f#8] = .ok () := rfl

-- Mixed valid 1/2/3/4-byte scalars (`U+0041`, `U+00A9`, `U+20AC`, `U+1F600`) -> `Ok ()`
example : runUtf8Validation
    [0x41#8, 0xc2#8, 0xa9#8, 0xe2#8, 0x82#8, 0xac#8, 0xf0#8, 0x9f#8, 0x98#8, 0x80#8] = .ok () := by
  decide

-- Boundary valid scalars: `U+0080` (`[0xC2, 0x80]`), `U+0800` (`[0xE0, 0xA0, 0x80]`),
-- `U+D7FF` (`[0xED, 0x9F, 0xBF]`), `U+E000` (`[0xEE, 0x80, 0x80]`),
-- `U+10000` (`[0xF0, 0x90, 0x80, 0x80]`), `U+10FFFF` (`[0xF4, 0x8F, 0xBF, 0xBF]`) -> `Ok ()`
example : runUtf8Validation
    [0xc2#8, 0x80#8,
     0xe0#8, 0xa0#8, 0x80#8,
     0xed#8, 0x9f#8, 0xbf#8,
     0xee#8, 0x80#8, 0x80#8,
     0xf0#8, 0x90#8, 0x80#8, 0x80#8,
     0xf4#8, 0x8f#8, 0xbf#8, 0xbf#8] = .ok () := by
  decide

-- Unexpected continuation byte at start `[0x80]` -> `Err { valid_up_to := 0, error_len := some 1 }`
example : runUtf8Validation [0x80#8] = .error { valid_up_to := 0, error_len := some 1#8 } := rfl

-- Overlong 2-byte (`0xC0 0xAF` for `'/'` and `0xC1 0xBF` for `U+007F`) -> `error_len = some 1`
example : runUtf8Validation [0xc0#8, 0xaf#8] = .error { valid_up_to := 0, error_len := some 1#8 } := rfl
example : runUtf8Validation [0xc1#8, 0xbf#8] = .error { valid_up_to := 0, error_len := some 1#8 } := rfl

-- Overlong 3-byte (`0xE0 0x9F 0xBF` for `U+07FF`) -> `error_len = some 1`
example : runUtf8Validation [0xe0#8, 0x9f#8, 0xbf#8] =
    .error { valid_up_to := 0, error_len := some 1#8 } := rfl

-- UTF-16 surrogates (`U+D800` = `0xED 0xA0 0x80` and `U+DFFF` = `0xED 0xBF 0xBF`) -> `error_len = some 1`
example : runUtf8Validation [0xed#8, 0xa0#8, 0x80#8] =
    .error { valid_up_to := 0, error_len := some 1#8 } := rfl
example : runUtf8Validation [0xed#8, 0xbf#8, 0xbf#8] =
    .error { valid_up_to := 0, error_len := some 1#8 } := rfl

-- Overlong 4-byte (`0xF0 0x8F 0xBF 0xBF` for `U+FFFF`) -> `error_len = some 1`
example : runUtf8Validation [0xf0#8, 0x8f#8, 0xbf#8, 0xbf#8] =
    .error { valid_up_to := 0, error_len := some 1#8 } := rfl

-- Above `U+10FFFF` (`0xF4 0x90 0x80 0x80` = `U+110000`, and `0xF5 0x80 0x80 0x80`) -> `error_len = some 1`
example : runUtf8Validation [0xf4#8, 0x90#8, 0x80#8, 0x80#8] =
    .error { valid_up_to := 0, error_len := some 1#8 } := rfl
example : runUtf8Validation [0xf5#8, 0x80#8, 0x80#8, 0x80#8] =
    .error { valid_up_to := 0, error_len := some 1#8 } := rfl

-- Invalid 3rd byte in 3-byte sequence after valid 2-byte prefix `"ok"` (`valid_up_to = 2`, `error_len = some 2`)
example : runUtf8Validation [0x6f#8, 0x6b#8, 0xe2#8, 0x82#8, 0x28#8] =
    .error { valid_up_to := 2, error_len := some 2#8 } := by
  decide

-- Invalid 4th byte in 4-byte sequence (`[0xF0, 0x9F, 0x98, 0x41]`) -> `error_len = some 3`
example : runUtf8Validation [0xf0#8, 0x9f#8, 0x98#8, 0x41#8] =
    .error { valid_up_to := 0, error_len := some 3#8 } := rfl

-- Truncated 2-byte, 3-byte, and 4-byte sequences at EOF -> `error_len = none`
example : runUtf8Validation [0x41#8, 0xc2#8] =
    .error { valid_up_to := 1, error_len := none } := rfl
example : runUtf8Validation [0x41#8, 0xe2#8, 0x82#8] =
    .error { valid_up_to := 1, error_len := none } := rfl
example : runUtf8Validation [0x41#8, 0xf0#8, 0x9f#8, 0x98#8] =
    .error { valid_up_to := 1, error_len := none } := rfl

-- Overlong NUL (`[0xC0, 0x80]`) -> `error_len = some 1`
example : runUtf8Validation [0xc0#8, 0x80#8] =
    .error { valid_up_to := 0, error_len := some 1#8 } := rfl

end Examples

end VerifiedLibraries.RustStd
