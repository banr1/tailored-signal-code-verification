/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
public meta import Mathlib.Tactic.ToAdditive
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Prefix-Stability and Delimited-Loop Lemmas for SPQR V1 Protobuf Decoding

Proves prefix-stability and error-overshoot properties (`ProtoPrefixStep`) for `LibsignalSpqrV1.Proto`
field and message decoders, relating an untruncated field-merge loop to slice-first
`Proto.mergeMessage` decoding.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Prost.MessageMerge.SymP3

open CryptoVerification.LibsignalSpqrV1 hiding WireType DecodeErr decodeVarint encodeVarint
open CryptoVerification.LibsignalSpqrV1.Proto

/-! ## `ProtoPrefixStep`: Prefix-Stability and Overshoot -/

/-- A parser `f : Bytes → Except DecodeErr (α × Bytes)` satisfies `ProtoPrefixStep` when:
1. (`ok_append`) If `f s = .ok (v, r')`, then `r'.length ≤ s.length` and
   `f (s ++ a) = .ok (v, r' ++ a)` for any trailing bytes `a`.
2. (`err_overshoot`) If `f s = .error e` fails on `s` alone, then it can only succeed on
   `s ++ a` (`f (s ++ a) = .ok (v, r)`) by reading past the end of `s` into `a`, leaving
   strictly fewer than `a.length` bytes (`r.length < a.length`). -/
structure ProtoPrefixStep {α : Type} (f : Bytes → Except DecodeErr (α × Bytes)) : Prop where
  ok_append : ∀ (s a : Bytes) (v : α) (r' : Bytes),
    f s = .ok (v, r') → r'.length ≤ s.length ∧ f (s ++ a) = .ok (v, r' ++ a)
  err_overshoot : ∀ (s a : Bytes) (e : DecodeErr) (v : α) (r : Bytes),
    f s = .error e → f (s ++ a) = .ok (v, r) → r.length < a.length

namespace ProtoPrefixStep

variable {α β : Type} {f : Bytes → Except DecodeErr (α × Bytes)}

theorem length_le (hf : ProtoPrefixStep f) {s : Bytes} {v : α} {r' : Bytes}
    (h : f s = .ok (v, r')) : r'.length ≤ s.length :=
  (hf.ok_append s [] v r' h).1

theorem append_eq_of_ok (hf : ProtoPrefixStep f) {s : Bytes} (a : Bytes) {v : α} {r' : Bytes}
    (h : f s = .ok (v, r')) : f (s ++ a) = .ok (v, r' ++ a) :=
  (hf.ok_append s a v r' h).2

/-- `ProtoPrefixStep` is closed under monadic bind. -/
theorem bind {g : α → Bytes → Except DecodeErr (β × Bytes)}
    (hf : ProtoPrefixStep f) (hg : ∀ x, ProtoPrefixStep (g x)) :
    ProtoPrefixStep (fun bs => do let (x, bs') ← f bs; g x bs') where
  ok_append s a y r'' h := by
    rcases hfs : f s with e | ⟨x, r'⟩
    · simp [hfs, Bind.bind, Except.bind] at h
    · simp only [hfs, Bind.bind, Except.bind] at h
      obtain ⟨hlen1, happ1⟩ := hf.ok_append s a x r' hfs
      obtain ⟨hlen2, happ2⟩ := (hg x).ok_append r' a y r'' h
      refine ⟨Nat.le_trans hlen2 hlen1, ?_⟩
      simp [happ1, happ2, Bind.bind, Except.bind]
  err_overshoot s a e y r'' h_err h_ok := by
    rcases hfa : f (s ++ a) with ea | ⟨x, r'⟩
    · simp [hfa, Bind.bind, Except.bind] at h_ok
    · simp only [hfa, Bind.bind, Except.bind] at h_ok
      rcases hfs : f s with es | ⟨x0, r0'⟩
      · have hlt1 := hf.err_overshoot s a es x r' hfs hfa
        have hle2 := (hg x).length_le h_ok
        omega
      · obtain ⟨_, happ1⟩ := hf.ok_append s a x0 r0' hfs
        rw [happ1] at hfa
        injection hfa with hpair
        injection hpair with hx hr
        subst hx hr
        simp only [hfs, Bind.bind, Except.bind] at h_err
        exact (hg x0).err_overshoot r0' a e y r'' h_err h_ok

theorem congr {f1 f2 : Bytes → Except DecodeErr (α × Bytes)}
    (hf : ProtoPrefixStep f1) (heq : ∀ bs, f1 bs = f2 bs) : ProtoPrefixStep f2 where
  ok_append s a v r' h := by
    rw [← heq s] at h
    rw [← heq (s ++ a)]
    exact hf.ok_append s a v r' h
  err_overshoot s a e v r h_err h_ok := by
    rw [← heq s] at h_err
    rw [← heq (s ++ a)] at h_ok
    exact hf.err_overshoot s a e v r h_err h_ok

/-- `ProtoPrefixStep` is closed under post-composition with a state-free check. -/
theorem bind_pure (hf : ProtoPrefixStep f) (k : α → Except DecodeErr β) :
    ProtoPrefixStep (fun bs => do let (x, bs') ← f bs; let y ← k x; .ok (y, bs')) where
  ok_append s a y r' h := by
    rcases hfs : f s with e | ⟨x, r0⟩
    · simp [hfs, Bind.bind, Except.bind] at h
    · simp only [hfs, Bind.bind, Except.bind] at h
      rcases hkx : k x with ek | y0
      · simp [hkx] at h
      · simp only [hkx, Except.ok.injEq, Prod.mk.injEq] at h
        rcases h with ⟨hy, hr⟩
        subst y0 r0
        obtain ⟨hlen, happ⟩ := hf.ok_append s a x r' hfs
        refine ⟨hlen, ?_⟩
        simp [happ, hkx, Bind.bind, Except.bind]
  err_overshoot s a e y r h_err h_ok := by
    rcases hfa : f (s ++ a) with ea | ⟨x, r0⟩
    · simp [hfa, Bind.bind, Except.bind] at h_ok
    · simp only [hfa, Bind.bind, Except.bind] at h_ok
      rcases hkx : k x with ek | y0
      · simp [hkx] at h_ok
      · simp only [hkx, Except.ok.injEq, Prod.mk.injEq] at h_ok
        rcases h_ok with ⟨hy, hr⟩
        subst y0 r0
        rcases hfs : f s with es | ⟨x0, r0'⟩
        · exact hf.err_overshoot s a es x r hfs hfa
        · obtain ⟨_, happ⟩ := hf.ok_append s a x0 r0' hfs
          rw [happ] at hfa
          injection hfa with hpair
          injection hpair with hx _
          subst hx
          simp [hfs, hkx, Bind.bind, Except.bind] at h_err

theorem map_fst (hf : ProtoPrefixStep f) (k : α → β) :
    ProtoPrefixStep (fun bs => do let (x, bs') ← f bs; .ok (k x, bs')) :=
  hf.bind_pure (fun x => .ok (k x))

theorem const_error (e : DecodeErr) :
    ProtoPrefixStep (fun _ : Bytes => (Except.error e : Except DecodeErr (α × Bytes))) where
  ok_append _ _ _ _ h := nomatch h
  err_overshoot _ _ _ _ _ _ h := nomatch h

theorem checkWireType_bind (expected actual : WireType) (hf : ProtoPrefixStep f) :
    ProtoPrefixStep (fun bs => do checkWireType expected actual; f bs) := by
  unfold checkWireType
  split
  · exact const_error _
  · exact hf

end ProtoPrefixStep

/-! ## Primitive `ProtoPrefixStep` Lemmas -/

theorem decodeVarintAux_length_lt (fuel idx : Nat) (acc : BitVec 64) (bs : Bytes)
    {v : BitVec 64} {rest : Bytes} (h : decodeVarintAux fuel idx acc bs = .ok (v, rest)) :
    rest.length < bs.length := by
  induction fuel generalizing idx acc bs with
  | zero => nomatch h
  | succ fuel ih =>
    cases bs with
    | nil => nomatch h
    | cons b tl =>
      simp only [decodeVarintAux] at h
      split at h
      · split at h
        · nomatch h
        · injection h with hpair; injection hpair with _ htl; subst htl; simp
      · split at h
        · injection h with hpair; injection hpair with _ htl; subst htl; simp
        · have hlt := ih (idx + 1) _ tl h; simp only [List.length_cons]; omega

theorem decodeVarint_length_lt {bs : Bytes} {v : BitVec 64} {rest : Bytes}
    (h : decodeVarint bs = .ok (v, rest)) : rest.length < bs.length :=
  decodeVarintAux_length_lt 10 0 0#64 bs h

theorem protoPrefixStep_decodeVarintAux (fuel idx : Nat) (acc : BitVec 64) :
    ProtoPrefixStep (decodeVarintAux fuel idx acc) := by
  induction fuel generalizing idx acc with
  | zero => exact ProtoPrefixStep.const_error .invalidVarint
  | succ fuel ih =>
    constructor
    · intro s a v r' h
      cases s with
      | nil => nomatch h
      | cons b tl =>
        simp only [decodeVarintAux, List.cons_append] at h ⊢
        split at h
        · rename_i h9; simp only [h9, ↓reduceIte]
          split at h
          · nomatch h
          · rename_i hlt2; simp only [hlt2, ↓reduceIte]
            injection h with hpair; injection hpair with hv hr; subst hv hr; exact ⟨by simp, rfl⟩
        · rename_i h9; simp only [h9]
          split at h
          · rename_i hlt80; simp only [hlt80, ↓reduceIte]
            injection h with hpair; injection hpair with hv hr; subst hv hr; exact ⟨by simp, rfl⟩
          · rename_i hlt80; simp only [hlt80, ↓reduceIte]
            obtain ⟨hlen, happ⟩ := (ih (idx + 1) _).ok_append tl a v r' h
            exact ⟨by simp only [List.length_cons]; omega, happ⟩
    · intro s a e v r h_err h_ok
      cases s with
      | nil =>
        simp only [List.nil_append] at h_ok
        exact decodeVarintAux_length_lt (fuel + 1) idx acc a h_ok
      | cons b tl =>
        simp only [decodeVarintAux, List.cons_append] at h_err h_ok
        split at h_err
        · rename_i h9; simp only [h9, ↓reduceIte] at h_ok
          split at h_err
          · rename_i hge2; simp [hge2] at h_ok
          · nomatch h_err
        · rename_i h9; simp only [h9] at h_ok
          split at h_err
          · nomatch h_err
          · rename_i hlt80; simp only [hlt80, ↓reduceIte] at h_ok
            exact (ih (idx + 1) _).err_overshoot tl a e v r h_err h_ok

theorem protoPrefixStep_decodeVarint : ProtoPrefixStep decodeVarint :=
  protoPrefixStep_decodeVarintAux 10 0 0#64

theorem decodeKey_length_lt {bs : Bytes} {tag : BitVec 32} {wt : WireType} {rest : Bytes}
    (h : decodeKey bs = .ok ((tag, wt), rest)) : rest.length < bs.length := by
  unfold decodeKey at h
  rcases hdv : decodeVarint bs with e | ⟨key, r0⟩
  · simp [hdv, Bind.bind, Except.bind] at h
  · simp only [hdv, Bind.bind, Except.bind] at h
    split at h
    · nomatch h
    · split at h
      · split at h
        · nomatch h
        · injection h with hpair; injection hpair with _ hr; subst hr
          exact decodeVarint_length_lt hdv
      · nomatch h

theorem protoPrefixStep_decodeKey : ProtoPrefixStep decodeKey where
  ok_append s a v r' h := by
    unfold decodeKey at h ⊢
    rcases hdv : decodeVarint s with e | ⟨key, r0⟩
    · simp [hdv, Bind.bind, Except.bind] at h
    · obtain ⟨hlen, happ⟩ := protoPrefixStep_decodeVarint.ok_append s a key r0 hdv
      simp only [hdv, happ, Bind.bind, Except.bind] at h ⊢
      split at h
      · nomatch h
      · rename_i hgt; simp only [hgt, ↓reduceIte]
        split at h
        · split at h
          · nomatch h
          · rename_i htag; simp only [htag, ↓reduceIte]
            injection h with hpair; injection hpair with hv hr; subst hv hr; exact ⟨hlen, rfl⟩
        · nomatch h
  err_overshoot s a e v r h_err h_ok := by
    unfold decodeKey at h_err h_ok
    rcases hdv_a : decodeVarint (s ++ a) with ea | ⟨key_a, r_a⟩
    · simp [hdv_a, Bind.bind, Except.bind] at h_ok
    · simp only [hdv_a, Bind.bind, Except.bind] at h_ok
      have hr_eq : r = r_a := by
        split at h_ok
        · nomatch h_ok
        · split at h_ok
          · split at h_ok
            · nomatch h_ok
            · injection h_ok with hpair; injection hpair with _ hr; exact hr.symm
          · nomatch h_ok
      subst hr_eq
      rcases hdv_s : decodeVarint s with es | ⟨key_s, r_s⟩
      · exact protoPrefixStep_decodeVarint.err_overshoot s a es key_a r hdv_s hdv_a
      · obtain ⟨_, happ⟩ := protoPrefixStep_decodeVarint.ok_append s a key_s r_s hdv_s
        rw [happ] at hdv_a
        injection hdv_a with hpair; injection hpair with hk _; subst hk
        simp only [hdv_s, Bind.bind, Except.bind] at h_err
        split at h_err
        · rename_i hgt; simp [hgt] at h_ok
        · rename_i hgt; simp only [hgt, ↓reduceIte] at h_ok
          split at h_err
          · rename_i wt hwt; rw [hwt] at h_ok; dsimp only at h_ok
            split at h_err
            · rename_i htag; simp [htag] at h_ok
            · nomatch h_err
          · rename_i hwt; rw [hwt] at h_ok; nomatch h_ok

theorem decodeKey_append_of_ok {s : Bytes} (a : Bytes) {tag : BitVec 32} {wt : WireType} {r' : Bytes}
    (h : decodeKey s = .ok ((tag, wt), r')) : decodeKey (s ++ a) = .ok ((tag, wt), r' ++ a) :=
  protoPrefixStep_decodeKey.append_eq_of_ok a h

theorem takeExact_eq_take_drop (n : Nat) (bs : Bytes) :
    takeExact n bs = if n ≤ bs.length then .ok (bs.take n, bs.drop n) else .error .bufferUnderflow := by
  induction n generalizing bs with
  | zero => simp [takeExact]
  | succ n ih =>
    cases bs with
    | nil => simp [takeExact]
    | cons b tl =>
      simp only [takeExact, ih tl, List.length_cons, Nat.add_le_add_iff_right,
        List.take_succ_cons, List.drop_succ_cons]
      split <;> rfl

theorem dropExact_eq_drop (n : Nat) (bs : Bytes) :
    dropExact n bs = if n ≤ bs.length then .ok (bs.drop n) else .error .bufferUnderflow := by
  induction n generalizing bs with
  | zero => simp [dropExact]
  | succ n ih =>
    cases bs with
    | nil => simp [dropExact]
    | cons b tl =>
      simp only [dropExact, ih tl, List.length_cons, Nat.add_le_add_iff_right, List.drop_succ_cons]

theorem protoPrefixStep_takeExact (n : Nat) : ProtoPrefixStep (takeExact n) where
  ok_append s a v r' h := by
    rw [takeExact_eq_take_drop] at h ⊢
    split at h
    · rename_i hle
      injection h with hpair; injection hpair with hv hr; subst hv hr
      have hle' : n ≤ (s ++ a).length := by simp; omega
      simp only [hle', ↓reduceIte, List.take_append_of_le_length hle,
        List.drop_append_of_le_length hle, List.length_drop]
      exact ⟨by omega, trivial⟩
    · nomatch h
  err_overshoot s a e v r h_err h_ok := by
    rw [takeExact_eq_take_drop] at h_err h_ok
    split at h_err
    · nomatch h_err
    · rename_i hgt
      split at h_ok
      · injection h_ok with hpair; injection hpair with _ hr; subst hr
        simp only [List.length_drop, List.length_append] at *; omega
      · nomatch h_ok

theorem protoPrefixStep_dropExact {α : Type} (n : Nat) (m : α) :
    ProtoPrefixStep (fun bs => do let r ← dropExact n bs; .ok (m, r)) where
  ok_append s a v r' h := by
    rw [dropExact_eq_drop] at h ⊢
    split at h
    · rename_i hle
      simp only [Bind.bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
      rcases h with ⟨hv, hr⟩; subst hv hr
      have hle' : n ≤ (s ++ a).length := by simp; omega
      simp only [hle', ↓reduceIte, Bind.bind, Except.bind,
        List.drop_append_of_le_length hle, List.length_drop]
      exact ⟨by omega, trivial⟩
    · simp [Bind.bind, Except.bind] at h
  err_overshoot s a e v r h_err h_ok := by
    rw [dropExact_eq_drop] at h_err h_ok
    split at h_err
    · simp [Bind.bind, Except.bind] at h_err
    · rename_i hgt
      split at h_ok
      · simp only [Bind.bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h_ok
        rcases h_ok with ⟨_, hr⟩
        subst hr
        simp only [List.length_drop, List.length_append] at *
        omega
      · simp [Bind.bind, Except.bind] at h_ok

/-! ## `skipField` and Scalar, Bytes, and Message Field Decoders -/

theorem protoPrefixStep_skipFieldNonGroup {α : Type} (wt : WireType) (m : α) :
    ProtoPrefixStep (fun bs => do let r ← skipFieldNonGroup wt bs; .ok (m, r)) := by
  cases wt <;> simp only [skipFieldNonGroup]
  case varint =>
    refine (protoPrefixStep_decodeVarint.map_fst (fun _ => m)).congr (fun bs => ?_)
    rcases decodeVarint bs with _ | ⟨_, _⟩ <;> rfl
  case ThirtyTwoBit =>
    exact protoPrefixStep_dropExact 4 m
  case SixtyFourBit =>
    exact protoPrefixStep_dropExact 8 m
  case lengthDelimited =>
    refine (protoPrefixStep_decodeVarint.bind (fun len => protoPrefixStep_dropExact len.toNat m)).congr (fun bs => ?_)
    rcases decodeVarint bs with _ | ⟨len, rest⟩
    · rfl
    · rcases dropExact len.toNat rest with _ | _ <;> rfl
  case startGroup =>
    exact ProtoPrefixStep.const_error .unexpectedEndGroupTag
  case endGroup =>
    exact ProtoPrefixStep.const_error .unexpectedEndGroupTag

theorem skipGroupLoop_length_lt
    {skipInner : WireType → BitVec 32 → Bytes → Except DecodeErr Bytes}
    (hInner : ∀ wt tag, ProtoPrefixStep (fun bs => do let r ← skipInner wt tag bs; .ok ((), r))) :
    ∀ (fuel : Nat) (groupTag : BitVec 32) (bs r : Bytes),
      skipGroupLoop skipInner fuel groupTag bs = .ok r → r.length < bs.length := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ h; nomatch h
  | succ fuel ih =>
    intro groupTag bs r h
    unfold skipGroupLoop at h
    rcases hdk : decodeKey bs with e | ⟨⟨innerTag, innerWt⟩, rest⟩
    · simp [hdk, Bind.bind, Except.bind] at h
    · have hlt1 : rest.length < bs.length := decodeKey_length_lt hdk
      simp only [hdk, Bind.bind, Except.bind] at h
      split at h
      · split at h
        · nomatch h
        · injection h with hr; subst hr; exact hlt1
      · rcases hsi : skipInner innerWt innerTag rest with e | rest'
        · simp [hsi] at h
        · simp only [hsi] at h
          have hle2 : rest'.length ≤ rest.length :=
            (hInner innerWt innerTag).length_le (v := ()) (by simp [hsi, Bind.bind, Except.bind])
          have hlt3 : r.length < rest'.length := ih groupTag rest' r h
          omega

theorem skipGroupLoop_prefix_aux
    {skipInner : WireType → BitVec 32 → Bytes → Except DecodeErr Bytes}
    (hInner : ∀ wt tag, ProtoPrefixStep (fun bs => do let r ← skipInner wt tag bs; .ok ((), r))) :
    ∀ (n : Nat) (s a : Bytes) (fuel1 fuel2 : Nat) (groupTag : BitVec 32),
      s.length ≤ n → s.length ≤ fuel1 → s.length ≤ fuel2 →
      ((∀ r', skipGroupLoop skipInner fuel1 groupTag s = .ok r' →
          r'.length < s.length ∧ skipGroupLoop skipInner fuel2 groupTag (s ++ a) = .ok (r' ++ a)) ∧
       (∀ e r, skipGroupLoop skipInner fuel1 groupTag s = .error e →
          skipGroupLoop skipInner fuel2 groupTag (s ++ a) = .ok r → r.length < a.length)) := by
  intro n
  induction n with
  | zero =>
    intro s a fuel1 fuel2 groupTag hlen _ _
    have hs : s = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hs
    refine ⟨?_, ?_⟩
    · intro r' h; cases fuel1 <;> nomatch h
    · intro e r _ h_ok
      rw [List.nil_append] at h_ok
      exact skipGroupLoop_length_lt hInner fuel2 groupTag a r h_ok
  | succ n ih =>
    intro s a fuel1 fuel2 groupTag hlen hfuel1 hfuel2
    cases s with
    | nil => exact ih [] a fuel1 fuel2 groupTag (by simp) (by simp) (by simp)
    | cons b tl =>
      have hpos : 0 < (b :: tl).length := by simp
      cases fuel1 with
      | zero => omega
      | succ f1 =>
        cases fuel2 with
        | zero => omega
        | succ f2 =>
          constructor
          · intro r' h
            unfold skipGroupLoop at h ⊢
            rcases hdk : decodeKey (b :: tl) with e | ⟨⟨innerTag, innerWt⟩, rest⟩
            · simp [hdk, Bind.bind, Except.bind] at h
            · have hlt1 : rest.length < (b :: tl).length := decodeKey_length_lt hdk
              have hdk_app := decodeKey_append_of_ok a hdk
              simp only [hdk, hdk_app, Bind.bind, Except.bind] at h ⊢
              split at h
              · rename_i heg
                simp only [heg, ↓reduceIte]
                split at h
                · nomatch h
                · rename_i htag
                  simp only [htag]
                  injection h with hr; subst hr
                  exact ⟨hlt1, rfl⟩
              · rename_i heg
                simp only [heg]
                rcases hsi : skipInner innerWt innerTag rest with e | rest'
                · simp [hsi] at h
                · simp only [hsi] at h
                  have hsi_unit : (do let r ← skipInner innerWt innerTag rest; (.ok ((), r) : Except DecodeErr (Unit × Bytes))) = .ok ((), rest') := by
                    simp [hsi, Bind.bind, Except.bind]
                  obtain ⟨hle2, hsi_app⟩ := (hInner innerWt innerTag).ok_append rest a () rest' hsi_unit
                  have hsi_app' : skipInner innerWt innerTag (rest ++ a) = .ok (rest' ++ a) := by
                    rcases h2 : skipInner innerWt innerTag (rest ++ a) with err | r2
                    · simp [h2, Bind.bind, Except.bind] at hsi_app
                    · simp only [h2, Bind.bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at hsi_app
                      rw [hsi_app.2]
                  simp only [hsi_app']
                  have hih := (ih rest' a f1 f2 groupTag
                    (by simp only [List.length_cons] at hlt1 hlen; omega)
                    (by simp only [List.length_cons] at hlt1 hfuel1; omega)
                    (by simp only [List.length_cons] at hlt1 hfuel2; omega)).1 r' h
                  exact ⟨by omega, hih.2⟩
          · intro e r h_err h_ok
            unfold skipGroupLoop at h_err h_ok
            rcases hdk_a : decodeKey ((b :: tl) ++ a) with ea | ⟨⟨innerTag, innerWt⟩, rest_a⟩
            · rw [hdk_a] at h_ok
              nomatch h_ok
            · rw [hdk_a] at h_ok
              dsimp only [Bind.bind, Except.bind] at h_ok
              rcases hdk_s : decodeKey (b :: tl) with es | ⟨⟨innerTag0, innerWt0⟩, rest⟩
              · have hlt_dk := protoPrefixStep_decodeKey.err_overshoot (b :: tl) a es (innerTag, innerWt) rest_a hdk_s hdk_a
                split at h_ok
                · split at h_ok
                  · nomatch h_ok
                  · injection h_ok with hr; subst hr; exact hlt_dk
                · rcases hsi_a : skipInner innerWt innerTag rest_a with esi | rest_a'
                  · rw [hsi_a] at h_ok; nomatch h_ok
                  · rw [hsi_a] at h_ok
                    have hle_si : rest_a'.length ≤ rest_a.length :=
                      (hInner innerWt innerTag).length_le (v := ()) (by simp [hsi_a, Bind.bind, Except.bind])
                    have hlt_loop := skipGroupLoop_length_lt hInner f2 groupTag rest_a' r h_ok
                    omega
              · have hlt1 : rest.length < (b :: tl).length := decodeKey_length_lt hdk_s
                have hdk_app := decodeKey_append_of_ok a hdk_s
                rw [hdk_app] at hdk_a
                injection hdk_a with hpair
                injection hpair with hkv hrest
                injection hkv with htag_eq hwt_eq
                subst htag_eq hwt_eq hrest
                simp only [hdk_s, Bind.bind, Except.bind] at h_err
                split at h_err
                · rename_i heg
                  simp only [heg, ↓reduceIte] at h_ok
                  split at h_err
                  · rename_i hne; simp [hne] at h_ok
                  · nomatch h_err
                · rename_i heg
                  simp only [heg] at h_ok
                  rcases hsi_a : skipInner innerWt0 innerTag0 (rest ++ a) with esi | rest_a'
                  · simp [hsi_a] at h_ok
                  · simp only [hsi_a] at h_ok
                    rcases hsi_s : skipInner innerWt0 innerTag0 rest with es | rest'
                    · have hlt_si : rest_a'.length < a.length :=
                        (hInner innerWt0 innerTag0).err_overshoot rest a es () rest_a'
                          (by simp [hsi_s, Bind.bind, Except.bind])
                          (by simp [hsi_a, Bind.bind, Except.bind])
                      have hlt_loop := skipGroupLoop_length_lt hInner f2 groupTag rest_a' r h_ok
                      omega
                    · simp only [hsi_s] at h_err
                      have hsi_unit : (do let r ← skipInner innerWt0 innerTag0 rest; (.ok ((), r) : Except DecodeErr (Unit × Bytes))) = .ok ((), rest') := by
                        simp [hsi_s, Bind.bind, Except.bind]
                      obtain ⟨hle2, hsi_app⟩ := (hInner innerWt0 innerTag0).ok_append rest a () rest' hsi_unit
                      have hsi_app' : rest_a' = rest' ++ a := by
                        simp only [hsi_a, Bind.bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at hsi_app
                        exact hsi_app.2
                      subst hsi_app'
                      exact (ih rest' a f1 f2 groupTag
                        (by simp only [List.length_cons] at hlt1 hlen; omega)
                        (by simp only [List.length_cons] at hlt1 hfuel1; omega)
                        (by simp only [List.length_cons] at hlt1 hfuel2; omega)).2 e r h_err h_ok

theorem protoPrefixStep_skipFieldAux_unit (depth : Nat) (wt : WireType) (tag : BitVec 32) :
    ProtoPrefixStep (fun bs => do let r ← skipFieldAux depth wt tag bs; .ok ((), r)) := by
  induction depth generalizing wt tag with
  | zero => exact ProtoPrefixStep.const_error .recursionLimitExceeded
  | succ depth' ih =>
    unfold skipFieldAux
    split
    · constructor
      · intro s a _ r' h
        rcases hsg : skipGroupLoop (skipFieldAux depth') s.length tag s with e | r0
        · simp [hsg, Bind.bind, Except.bind] at h
        · simp only [hsg, Bind.bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
          rcases h with ⟨_, hr⟩
          subst r0
          obtain ⟨hlt, happ⟩ :=
            (skipGroupLoop_prefix_aux ih s.length s a s.length (s ++ a).length tag
              (Nat.le_refl _) (Nat.le_refl _) (by simp)).1 r' hsg
          refine ⟨Nat.le_of_lt hlt, ?_⟩
          rw [happ]; rfl
      · intro s a e _ r h_err h_ok
        rcases hsg_s : skipGroupLoop (skipFieldAux depth') s.length tag s with es | r0
        · rcases hsg_a : skipGroupLoop (skipFieldAux depth') (s ++ a).length tag (s ++ a) with ea | ra
          · rw [hsg_a] at h_ok
            nomatch h_ok
          · rw [hsg_a] at h_ok
            simp only [Bind.bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h_ok
            rcases h_ok with ⟨_, hr⟩
            subst ra
            exact (skipGroupLoop_prefix_aux ih s.length s a s.length (s ++ a).length tag
              (Nat.le_refl _) (Nat.le_refl _) (by simp)).2 es r hsg_s hsg_a
        · simp [hsg_s, Bind.bind, Except.bind] at h_err
    · exact protoPrefixStep_skipFieldNonGroup wt ()

theorem protoPrefixStep_skipField {α : Type} (wt : WireType) (tag : BitVec 32) (depth : Nat) (m : α) :
    ProtoPrefixStep (fun bs => do let r ← skipField wt tag bs depth; .ok (m, r)) where
  ok_append s a v r' h := by
    rcases hsf : skipField wt tag s depth with e | r0
    · simp [hsf, Bind.bind, Except.bind] at h
    · simp only [hsf, Bind.bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
      rcases h with ⟨hv, hr⟩
      subst hv r0
      have hunit : (do let r ← skipFieldAux depth wt tag s; (.ok ((), r) : Except DecodeErr (Unit × Bytes))) = .ok ((), r') := by
        change (do let r ← skipField wt tag s depth; (.ok ((), r) : Except DecodeErr (Unit × Bytes))) = .ok ((), r')
        simp [hsf, Bind.bind, Except.bind]
      obtain ⟨hlen, happ⟩ := (protoPrefixStep_skipFieldAux_unit depth wt tag).ok_append s a () r' hunit
      refine ⟨hlen, ?_⟩
      rcases h2 : skipField wt tag (s ++ a) depth with e2 | r2
      · change skipFieldAux depth wt tag (s ++ a) = .error e2 at h2
        simp [h2, Bind.bind, Except.bind] at happ
      · change skipFieldAux depth wt tag (s ++ a) = .ok r2 at h2
        simp only [h2, Bind.bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at happ
        rw [← happ.2]; rfl
  err_overshoot s a e v r h_err h_ok := by
    rcases hsf_s : skipField wt tag s depth with es | r0
    · rcases hsf_a : skipField wt tag (s ++ a) depth with ea | ra
      · simp [hsf_a, Bind.bind, Except.bind] at h_ok
      · simp only [hsf_a, Bind.bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h_ok
        rcases h_ok with ⟨_, hr⟩
        subst ra
        exact (protoPrefixStep_skipFieldAux_unit depth wt tag).err_overshoot s a es () r
          (by change (do let r ← skipField wt tag s depth; _) = _; simp [hsf_s, Bind.bind, Except.bind])
          (by change (do let r ← skipField wt tag (s ++ a) depth; _) = _; simp [hsf_a, Bind.bind, Except.bind])
    · simp [hsf_s, Bind.bind, Except.bind] at h_err

theorem protoPrefixStep_mergeUint32 (wt : WireType) :
    ProtoPrefixStep (mergeUint32 wt) := by
  unfold mergeUint32
  exact ProtoPrefixStep.checkWireType_bind .varint wt
    (protoPrefixStep_decodeVarint.map_fst (fun v => v.truncate 32))

theorem protoPrefixStep_mergeUint64 (wt : WireType) :
    ProtoPrefixStep (mergeUint64 wt) := by
  unfold mergeUint64
  exact ProtoPrefixStep.checkWireType_bind .varint wt protoPrefixStep_decodeVarint

theorem protoPrefixStep_mergeInt32 (wt : WireType) :
    ProtoPrefixStep (mergeInt32 wt) := by
  unfold mergeInt32
  exact ProtoPrefixStep.checkWireType_bind .varint wt
    (protoPrefixStep_decodeVarint.map_fst (fun v => v.truncate 32))

theorem protoPrefixStep_mergeBool (wt : WireType) :
    ProtoPrefixStep (mergeBool wt) := by
  unfold mergeBool
  exact ProtoPrefixStep.checkWireType_bind .varint wt
    (protoPrefixStep_decodeVarint.map_fst (fun v => v != 0#64))

theorem protoPrefixStep_mergeBytes (wt : WireType) :
    ProtoPrefixStep (mergeBytes wt) := by
  unfold mergeBytes
  exact ProtoPrefixStep.checkWireType_bind .lengthDelimited wt
    (protoPrefixStep_decodeVarint.bind (fun len => protoPrefixStep_takeExact len.toNat))

theorem protoPrefixStep_mergeRepeatedBytes (wt : WireType) (vals : List Bytes) :
    ProtoPrefixStep (mergeRepeatedBytes wt vals) := by
  unfold mergeRepeatedBytes
  exact (protoPrefixStep_mergeBytes wt).map_fst (fun b => vals ++ [b])

theorem protoPrefixStep_mergeMessage {M : Type}
    (mergeField : M → BitVec 32 → WireType → Bytes → Nat → Except DecodeErr (M × Bytes))
    (wt : WireType) (m : M) (depth : Nat) :
    ProtoPrefixStep (fun bs => mergeMessage mergeField wt m bs depth) := by
  unfold mergeMessage
  apply ProtoPrefixStep.checkWireType_bind .lengthDelimited wt
  cases depth with
  | zero => exact ProtoPrefixStep.const_error .recursionLimitExceeded
  | succ depth' =>
    exact protoPrefixStep_decodeVarint.bind (fun len =>
      (protoPrefixStep_takeExact len.toNat).bind_pure (fun sub =>
        mergeFieldsLoop mergeField sub.length m sub depth'))

theorem protoPrefixStep_mergeOptMessage {M : Type} [Inhabited M]
    (mergeField : M → BitVec 32 → WireType → Bytes → Nat → Except DecodeErr (M × Bytes))
    (wt : WireType) (opt : Option M) (depth : Nat) :
    ProtoPrefixStep (fun bs => mergeOptMessage mergeField wt opt bs depth) := by
  unfold mergeOptMessage
  exact (protoPrefixStep_mergeMessage mergeField wt (opt.getD default) depth).map_fst some

theorem protoPrefixStep_mergeRepeatedMessage {M : Type} [Inhabited M]
    (mergeField : M → BitVec 32 → WireType → Bytes → Nat → Except DecodeErr (M × Bytes))
    (wt : WireType) (ms : List M) (depth : Nat) :
    ProtoPrefixStep (fun bs => mergeRepeatedMessage mergeField wt ms bs depth) := by
  unfold mergeRepeatedMessage
  exact (protoPrefixStep_mergeMessage mergeField wt default depth).map_fst (fun m' => ms ++ [m'])

/-! ## `mergeFieldsLoop` Fuel Invariance and Step Lemmas -/

theorem mergeFieldsLoop_fuel {M : Type}
    {mergeField : M → BitVec 32 → WireType → Bytes → Nat → Except DecodeErr (M × Bytes)}
    (hmf : ∀ m tag wt depth', ProtoPrefixStep (fun bs => mergeField m tag wt bs depth')) :
    ∀ (n : Nat) (bs : Bytes) (fuel1 fuel2 : Nat) (m : M) (depth' : Nat),
      bs.length ≤ n → bs.length ≤ fuel1 → bs.length ≤ fuel2 →
      mergeFieldsLoop mergeField fuel1 m bs depth' =
        mergeFieldsLoop mergeField fuel2 m bs depth' := by
  intro n
  induction n with
  | zero =>
    intro bs fuel1 fuel2 m depth' hlen _ _
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    cases fuel1 <;> cases fuel2 <;> rfl
  | succ n ih =>
    intro bs fuel1 fuel2 m depth' hlen hf1 hf2
    cases bs with
    | nil =>
      cases fuel1 <;> cases fuel2 <;> rfl
    | cons b tl =>
      have hpos : 0 < (b :: tl).length := by simp
      cases fuel1 with
      | zero => omega
      | succ f1 =>
        cases fuel2 with
        | zero => omega
        | succ f2 =>
          simp only [mergeFieldsLoop]
          rcases hdk : decodeKey (b :: tl) with e | ⟨⟨tag, wt⟩, rest⟩
          · rfl
          · have hlt1 : rest.length < (b :: tl).length := decodeKey_length_lt hdk
            dsimp only [Bind.bind, Except.bind]
            rcases hstep : mergeField m tag wt rest depth' with e | ⟨m', rest'⟩
            · rfl
            · have hle2 : rest'.length ≤ rest.length :=
                (hmf m tag wt depth').length_le hstep
              exact ih rest' f1 f2 m' depth' (by omega) (by omega) (by omega)

theorem mergeFieldsLoop_step_of_ok {M : Type}
    {mergeField : M → BitVec 32 → WireType → Bytes → Nat → Except DecodeErr (M × Bytes)}
    (hmf : ∀ m tag wt depth', ProtoPrefixStep (fun bs => mergeField m tag wt bs depth'))
    {s rest_s rest'_s : Bytes} (m m' : M) (depth' : Nat) {tag : BitVec 32} {wt : WireType}
    (hdk_s : decodeKey s = .ok ((tag, wt), rest_s))
    (hmf_s : mergeField m tag wt rest_s depth' = .ok (m', rest'_s)) :
    rest'_s.length < s.length ∧
      mergeFieldsLoop mergeField s.length m s depth' =
        mergeFieldsLoop mergeField rest'_s.length m' rest'_s depth' := by
  cases s with
  | nil => nomatch hdk_s
  | cons b tl =>
    have hlt1 : rest_s.length < (b :: tl).length := decodeKey_length_lt hdk_s
    have hle2 : rest'_s.length ≤ rest_s.length := (hmf m tag wt depth').length_le hmf_s
    refine ⟨by omega, ?_⟩
    simp only [mergeFieldsLoop, List.length_cons, hdk_s, hmf_s, Bind.bind, Except.bind]
    exact mergeFieldsLoop_fuel hmf rest'_s.length rest'_s tl.length rest'_s.length m' depth'
      (Nat.le_refl _) (by simp only [List.length_cons] at hlt1; omega) (Nat.le_refl _)

/-! ## Concrete `ProtoPrefixStep` Instances for SPQR Protobuf Messages -/

theorem ProtoPrefixStep.ite {α : Type} (c : Prop) [Decidable c]
    {f g : Bytes → Except DecodeErr (α × Bytes)}
    (hf : ProtoPrefixStep f) (hg : ProtoPrefixStep g) :
    ProtoPrefixStep (fun bs => if c then f bs else g bs) := by
  by_cases hc : c <;> simp only [hc, ↓reduceIte] <;> assumption

theorem ProtoPrefixStep.bind_ok {α β : Type} {f : Bytes → Except DecodeErr (α × Bytes)}
    (hf : ProtoPrefixStep f) {k : α × Bytes → Except DecodeErr (β × Bytes)}
    (hk : ∀ v r1 r2 m' r', k (v, r1) = .ok (m', r') → r' = r1 ∧ k (v, r2) = .ok (m', r2))
    (herr : ∀ v r1 r2 e, k (v, r1) = .error e → k (v, r2) = .error e) :
    ProtoPrefixStep (fun bs => Bind.bind (f bs) k) where
  ok_append s a v r' h := by
    rcases hf_s : f s with e | ⟨v0, r0⟩
    · simp [hf_s, Bind.bind, Except.bind] at h
    · simp only [hf_s, Bind.bind, Except.bind] at h
      obtain ⟨rfl, hk_app⟩ := hk v0 r0 (r0 ++ a) v r' h
      obtain ⟨hlen, hf_app⟩ := hf.ok_append s a v0 r' hf_s
      refine ⟨hlen, ?_⟩
      simp only [hf_app, Bind.bind, Except.bind, hk_app]
  err_overshoot s a e v r h_err h_ok := by
    rcases hf_a : f (s ++ a) with ea | ⟨va, ra⟩
    · simp [hf_a, Bind.bind, Except.bind] at h_ok
    · simp only [hf_a, Bind.bind, Except.bind] at h_ok
      obtain ⟨rfl, _⟩ := hk va ra ra v r h_ok
      rcases hf_s : f s with es | ⟨vs, rs⟩
      · exact hf.err_overshoot s a es va r hf_s hf_a
      · simp only [hf_s, Bind.bind, Except.bind] at h_err
        obtain ⟨_, hf_app⟩ := hf.ok_append s a vs rs hf_s
        rw [hf_app] at hf_a
        injection hf_a with hpair; injection hpair with hvs hrs; subst hvs hrs
        have herr_a := herr vs rs (rs ++ a) e h_err
        rw [herr_a] at h_ok; nomatch h_ok

macro "close_proto_prefix_field" : tactic =>
  `(tactic|
    repeat' first
      | refine ProtoPrefixStep.ite _ ?_ ?_
      | exact ProtoPrefixStep.bind_ok (protoPrefixStep_mergeUint32 _) (by rintro _ _ _ _ _ ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩) (by rintro _ _ _ _ ⟨⟩)
      | exact ProtoPrefixStep.bind_ok (protoPrefixStep_mergeUint64 _) (by rintro _ _ _ _ _ ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩) (by rintro _ _ _ _ ⟨⟩)
      | exact ProtoPrefixStep.bind_ok (protoPrefixStep_mergeInt32 _) (by rintro _ _ _ _ _ ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩) (by rintro _ _ _ _ ⟨⟩)
      | exact ProtoPrefixStep.bind_ok (protoPrefixStep_mergeBool _) (by rintro _ _ _ _ _ ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩) (by rintro _ _ _ _ ⟨⟩)
      | exact ProtoPrefixStep.bind_ok (protoPrefixStep_mergeBytes _) (by rintro _ _ _ _ _ ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩) (by rintro _ _ _ _ ⟨⟩)
      | exact ProtoPrefixStep.bind_ok (protoPrefixStep_mergeRepeatedBytes _ _) (by rintro _ _ _ _ _ ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩) (by rintro _ _ _ _ ⟨⟩)
      | exact ProtoPrefixStep.bind_ok (protoPrefixStep_mergeMessage _ _ _ _) (by rintro _ _ _ _ _ ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩) (by rintro _ _ _ _ ⟨⟩)
      | exact ProtoPrefixStep.bind_ok (protoPrefixStep_mergeOptMessage _ _ _ _) (by rintro _ _ _ _ _ ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩) (by rintro _ _ _ _ ⟨⟩)
      | exact ProtoPrefixStep.bind_ok (protoPrefixStep_mergeRepeatedMessage _ _ _ _) (by rintro _ _ _ _ _ ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩) (by rintro _ _ _ _ ⟨⟩)
      | exact protoPrefixStep_skipField _ _ _ _)

theorem protoPrefixStep_chainParamsPB_mergeField (m : ChainParamsPB) (tag : BitVec 32) (wt : WireType) (depth : Nat) :
    ProtoPrefixStep (fun bs => ChainParamsPB.mergeField m tag wt bs depth) := by
  unfold ChainParamsPB.mergeField; close_proto_prefix_field
theorem protoPrefixStep_chainPB_mergeField (m : ChainPB) (tag : BitVec 32) (wt : WireType) (depth : Nat) :
    ProtoPrefixStep (fun bs => ChainPB.mergeField m tag wt bs depth) := by
  unfold ChainPB.mergeField; close_proto_prefix_field
theorem protoPrefixStep_versionNegotiationPB_mergeField (m : VersionNegotiationPB) (tag : BitVec 32) (wt : WireType) (depth : Nat) :
    ProtoPrefixStep (fun bs => VersionNegotiationPB.mergeField m tag wt bs depth) := by
  unfold VersionNegotiationPB.mergeField; close_proto_prefix_field
theorem protoPrefixStep_protoAuthenticator_mergeField (m : ProtoAuthenticator) (tag : BitVec 32) (wt : WireType) (depth : Nat) :
    ProtoPrefixStep (fun bs => ProtoAuthenticator.mergeField m tag wt bs depth) := by
  unfold ProtoAuthenticator.mergeField; close_proto_prefix_field
theorem protoPrefixStep_unchunked_noHeaderReceived_mergeField (m : V1State.Unchunked.NoHeaderReceived) (tag : BitVec 32) (wt : WireType) (depth : Nat) :
    ProtoPrefixStep (fun bs => V1State.Unchunked.NoHeaderReceived.mergeField m tag wt bs depth) := by
  unfold V1State.Unchunked.NoHeaderReceived.mergeField; close_proto_prefix_field
theorem protoPrefixStep_chunked_noHeaderReceived_mergeField (m : V1State.Chunked.NoHeaderReceived) (tag : BitVec 32) (wt : WireType) (depth : Nat) :
    ProtoPrefixStep (fun bs => V1State.Chunked.NoHeaderReceived.mergeField m tag wt bs depth) := by
  unfold V1State.Chunked.NoHeaderReceived.mergeField; close_proto_prefix_field
theorem protoPrefixStep_v1State_innerState_merge (cur : Option V1State.InnerState) (tag : BitVec 32) (wt : WireType) (depth : Nat) :
    ProtoPrefixStep (fun bs => V1State.InnerState.merge cur tag wt bs depth) := by
  unfold V1State.InnerState.merge; close_proto_prefix_field
theorem protoPrefixStep_v1State_mergeField (m : V1State) (tag : BitVec 32) (wt : WireType) (depth : Nat) :
    ProtoPrefixStep (fun bs => V1State.mergeField m tag wt bs depth) := by
  unfold V1State.mergeField
  refine ProtoPrefixStep.ite _ ?_ ?_
  · exact ProtoPrefixStep.bind_ok (protoPrefixStep_v1State_innerState_merge m.innerState tag wt depth)
      (by rintro _ _ _ _ _ ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩) (by rintro _ _ _ _ ⟨⟩)
  · exact protoPrefixStep_skipField wt tag depth m
theorem protoPrefixStep_pqRatchetState_inner_merge (cur : Option PqRatchetState.Inner) (tag : BitVec 32) (wt : WireType) (depth : Nat) :
    ProtoPrefixStep (fun bs => PqRatchetState.Inner.merge cur tag wt bs depth) := by
  unfold PqRatchetState.Inner.merge; close_proto_prefix_field
theorem protoPrefixStep_pqRatchetState_mergeField (m : PqRatchetState) (tag : BitVec 32) (wt : WireType) (depth : Nat) :
    ProtoPrefixStep (fun bs => PqRatchetState.mergeField m tag wt bs depth) := by
  unfold PqRatchetState.mergeField
  repeat' first
    | refine ProtoPrefixStep.ite _ ?_ ?_
    | exact ProtoPrefixStep.bind_ok (protoPrefixStep_mergeOptMessage _ wt _ depth)
        (by rintro _ _ _ _ _ ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩) (by rintro _ _ _ _ ⟨⟩)
    | exact ProtoPrefixStep.bind_ok (protoPrefixStep_pqRatchetState_inner_merge m.inner tag wt depth)
        (by rintro _ _ _ _ _ ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩) (by rintro _ _ _ _ ⟨⟩)
    | exact protoPrefixStep_skipField wt tag depth m

end CryptoVerification.SpqrV1.Prost.MessageMerge.SymP3
