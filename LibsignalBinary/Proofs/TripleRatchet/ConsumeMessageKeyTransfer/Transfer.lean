/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.TrapRng
public import LibsignalBinary.Proofs.Placed.PlacedCallSym
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.SpecLemmas.LibsignalSessionProofDefs

/-!
# Monotone Hook-Map Transfer for `subroutine_ok`

Proves that `subroutine_ok (P.rebase b X1) e spec` lifts to `P.rebase b X2` whenever `X2` extends
`X1` pointwise (`X1 n = some f → X2 n = some f`), stub offsets of `P` are pairwise distinct
(`allFreshOffsets`), and every stub's code word fails to decode (`StubsDead`). Any stub unhooked in
`X1` halts with `halt_unmapped`, so a run reaching a `subroutine_ok` outcome never visits it.

Instantiates this transfer for `libsignalSessionCode` (where every stub word is zero and checked by
`rfl_kernel`), lifting `sessionExterns` contracts to `tripleRatchetExterns`, and provides
relocatable `[LibsignalPlacement]` block-to-block transfer lemmas.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.LibsignalTripleRatchetRepr

/-! ## Generic part -/

/-- Every stub of `P` sits on a code word that does not decode. -/
def StubsDead (P : Program) : Prop :=
  ∀ n o, (n, o) ∈ P.stubs → ∃ w, P.readWordOff o = some w ∧ decode w = none

/-- With the code loaded, the 32-bit memory word at `base + off` is the code word at `off`. -/
theorem read32_of_readWordOff {prog : Program} {m : Memory} {off : Nat} {w : BitVec 32}
    (hL : prog.CodeLoaded m) (h : prog.readWordOff off = some w) :
    m.read32 (prog.base + BitVec.ofNat 64 off) = w := by
  obtain ⟨_, _, hcode⟩ := Program.codeLoaded_iff.1 hL
  unfold Program.readWordOff at h
  split at h
  · contradiction
  split at h
  · rename_i b0 b1 b2 b3 tl hdrop
    simp only [Option.some.injEq] at h
    subst h
    have hlen4 : off + 4 ≤ prog.code.length := by
      have := congrArg List.length hdrop
      simp at this; omega
    have hb : ∀ k (hk : k < 4),
        m.read8 (prog.base + BitVec.ofNat 64 off + BitVec.ofNat 64 k) = prog.code[off + k] := by
      intro k hk
      have e : prog.base + BitVec.ofNat 64 off + BitVec.ofNat 64 k =
          prog.base + BitVec.ofNat 64 (off + k) := by
        rw [BitVec.ofNat_add, BitVec.add_assoc]
      rw [e]; exact (hcode (off + k) (by omega)).1
    have hget : ∀ k (hk : k < 4),
        prog.code[off + k] = (b0 :: b1 :: b2 :: b3 :: tl)[k]'(by simp; omega) := by
      intro k hk
      simp only [← hdrop, List.getElem_drop]
    have h0 := hb 0 (by omega); have h1 := hb 1 (by omega)
    have h2 := hb 2 (by omega); have h3 := hb 3 (by omega)
    have g0 := hget 0 (by omega); have g1 := hget 1 (by omega)
    have g2 := hget 2 (by omega); have g3 := hget 3 (by omega)
    simp only [Memory.read32]
    simp only [List.getElem_cons_succ, List.getElem_cons_zero] at g0 g1 g2 g3
    rw [show (0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, h0, g0,
      show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, h1, g1,
      show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, h2, g2,
      show (3#64 : BitVec 64) = BitVec.ofNat 64 3 from rfl, h3, g3]
  · contradiction

/-- A hook of a rebased program (no overrides) comes from a stub at the pc's offset. -/
theorem stub_of_externAt? {P : Program} {b : BitVec 64} {X : String → Option (State → State)}
    {pc : BitVec 64} {f : State → State}
    (h : (P.rebase b X).externAt? pc = some f) :
    ∃ n, (n, (pc - b).toNat) ∈ P.stubs ∧ X n = some f := by
  unfold Program.externAt? Program.hookAtOff? at h
  simp only [Program.rebase_stubs, Program.rebase_externs, Program.rebase_symbols,
    Program.rebase_overrides, Program.rebase_base] at h
  have hsym : (P.symbols.findSome? fun (_ : String × Nat) => (none : Option (State → State))) =
      none :=
    Program.findSome?_eq_none_of_forall fun _ _ => rfl
  simp only [ite_self] at h
  rw [hsym, Option.or_none] at h
  obtain ⟨⟨n, o⟩, hmem, hx⟩ := List.exists_of_findSome?_eq_some h
  simp only at hx
  split at hx
  · rename_i ho
    have : o = (pc - b).toNat := beq_iff_eq.mp ho
    subst this
    exact ⟨n, hmem, hx⟩
  · contradiction

/-- Hooks of `P.rebase b X1` are hooks of `P.rebase b X2` when `X2` extends `X1`. -/
theorem externAt?_mono {P : Program} {b : BitVec 64} {X1 X2 : String → Option (State → State)}
    (hfresh : allFreshOffsets P.stubs = true)
    (hle : ∀ n f, X1 n = some f → X2 n = some f)
    {pc : BitVec 64} {f : State → State}
    (h : (P.rebase b X1).externAt? pc = some f) :
    (P.rebase b X2).externAt? pc = some f := by
  obtain ⟨n, hmem, hx⟩ := stub_of_externAt? h
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hmem
  have hk' : (P.rebase b X2).stubs[k]? = some (n, (pc - b).toNat) := by
    rw [Program.rebase_stubs]; exact hk
  have hh := hookAtOff?_of_stub (prog := P.rebase b X2)
    (by rw [Program.rebase_stubs]; exact hfresh) (fun _ => rfl) k hk'
  unfold Program.externAt?
  rw [Program.rebase_base, hh, Program.rebase_externs]
  exact hle n f hx

/-- An instruction fetched from loaded code of `P.rebase b X1` is fetched by `P.rebase b X2`:
an extra hook of `X2` sits on a stub whose word does not decode. -/
theorem fetchMem_mono {P : Program} {b : BitVec 64} {X1 X2 : String → Option (State → State)}
    (hdead : StubsDead P)
    {m : Memory} (hL : (P.rebase b X1).CodeLoaded m) {pc : BitVec 64} {inst : Instr}
    (h : (P.rebase b X1).fetchMem m pc = some inst) :
    (P.rebase b X2).fetchMem m pc = some inst := by
  unfold Program.fetchMem at h ⊢
  split at h
  · contradiction
  by_cases hx2 : ((P.rebase b X2).externAt? pc).isSome
  · exfalso
    obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 hx2
    obtain ⟨n, hmem, _⟩ := stub_of_externAt? hg
    obtain ⟨w, hw, hdec⟩ := hdead n _ hmem
    have hr := read32_of_readWordOff hL (by rw [Program.readWordOff_rebase]; exact hw)
    have hpc : (P.rebase b X1).base + BitVec.ofNat 64 (pc - b).toNat = pc := by
      rw [Program.rebase_base, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm,
        BitVec.sub_add_cancel]
    rw [hpc] at hr
    split at h
    · contradiction
    split at h
    · contradiction
    rw [hr, hdec] at h
    contradiction
  · simp only [Bool.not_eq_true] at hx2
    simp only [hx2, Bool.false_eq_true, ↓reduceIte]
    exact h

/-- `Steps` of `P.rebase b X1` ending in a non-halted state, from loaded code, are `Steps` of
`P.rebase b X2`. -/
theorem steps_mono {P : Program} {b : BitVec 64} {X1 X2 : String → Option (State → State)}
    (hfresh : allFreshOffsets P.stubs = true) (hdead : StubsDead P)
    (hle : ∀ n f, X1 n = some f → X2 n = some f)
    {s s' : State} (hs : Steps (P.rebase b X1) s s') (hL : (P.rebase b X1).CodeLoaded s.mem)
    (hnh : s'.status ≠ .Halted) :
    Steps (P.rebase b X2) s s' := by
  induction hs with
  | refl s => exact Steps.refl s
  | @step sa sb sc h1 hrest ih =>
    have hLb : (P.rebase b X1).CodeLoaded sb.mem := h1.codeLoaded hL
    cases h1 with
    | exec hrun hf =>
      exact Steps.step (Step.exec hrun (fetchMem_mono hdead hL hf)) (ih hLb hnh)
    | halt_unmapped _ _ _ =>
      have heq := hrest.eq_of_halted rfl
      subst heq
      exact absurd rfl hnh
    | extern hrun he hk hsym =>
      exact Steps.step (Step.extern hrun (externAt?_mono hfresh hle he) hk hsym) (ih hLb hnh)
    | extern_fault hrun he hnk =>
      exact Steps.step (Step.extern_fault hrun (externAt?_mono hfresh hle he) hnk) (ih hLb hnh)

/-- `subroutine_ok` on `P.rebase b X1` lifts to `P.rebase b X2` when `X2` extends `X1`, stub
offsets are pairwise distinct, and no stub word decodes. -/
theorem subroutine_ok_rebase_mono {α : Type} {P : Program} {b : BitVec 64}
    {X1 X2 : String → Option (State → State)}
    (hfresh : allFreshOffsets P.stubs = true) (hdead : StubsDead P)
    (hle : ∀ n f, X1 n = some f → X2 n = some f)
    {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok (P.rebase b X1) entry spec) :
    subroutine_ok (P.rebase b X2) entry spec := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hal hL2 => ?_
  have hL1 : (P.rebase b X1).CodeLoaded s0.mem := by
    rw [Program.codeLoaded_iff] at hL2 ⊢
    dsimp only [Program.rebase] at hL2 ⊢
    exact hL2
  obtain ⟨sf, hs, hout, -⟩ := h.no_fault_before_outcome x R s0 hpc hrun hpre hal hL1
  have hnh : sf.status ≠ .Halted := by
    rcases hout with ⟨⟨_, _, hr⟩, _, _⟩ | ⟨hp, _⟩ | ⟨code, he, _⟩ | ⟨ho, _⟩
    · rw [hr]; intro h; injection h
    · rw [hp]; intro h; injection h
    · rw [he]; intro h; injection h
    · rw [ho]; intro h; injection h
  exact reaches_outcome_steps (steps_mono hfresh hdead hle hs hL1 hnh)
    (reaches_outcome.of_outcome hout)

/-- `Rust.withPanics` preserves the extension order of hook maps. -/
theorem withPanics_mono {X1 X2 : String → Option (State → State)}
    (hle : ∀ n f, X1 n = some f → X2 n = some f) :
    ∀ n f, Rust.withPanics X1 n = some f → Rust.withPanics X2 n = some f := by
  intro n f h
  unfold Rust.withPanics at h ⊢
  split
  · rename_i hp; simp only [hp, ↓reduceIte] at h; exact h
  · rename_i hp; simp only [hp, Bool.false_eq_true, ↓reduceIte] at h; exact hle n f h

/-! ## Session instance -/

private theorem drop_all_toBytesAux' :
    ∀ (t : WordTree) {n : Nat} (acc : List (BitVec 8)),
      t.checkSize? = some n → (t.toBytesAux acc).drop (4 * n) = acc
  | .empty, _, acc, h => by
    simp only [WordTree.checkSize?, Option.some.injEq] at h
    subst h; rfl
  | .leaf _ _ _ _, _, acc, h => by
    simp only [WordTree.checkSize?, Option.some.injEq] at h
    subst h; rfl
  | .node lw l r, _, acc, h => by
    simp only [WordTree.checkSize?] at h
    split at h <;> try contradiction
    rename_i nl nr hl hr
    split at h <;> try contradiction
    simp only [Option.some.injEq] at h
    subst h
    rw [WordTree.toBytesAux, Nat.mul_add, ← List.drop_drop,
      drop_all_toBytesAux' l (r.toBytesAux acc) hl, drop_all_toBytesAux' r acc hr]

private theorem getQuad?_drop_toBytesAux' {b0 b1 b2 b3 : BitVec 8} :
    ∀ (t : WordTree) {n : Nat} (acc : List (BitVec 8)) (j : Nat),
      t.checkSize? = some n → t.getQuad? j = some (b0, b1, b2, b3) →
      ∃ rest, (t.toBytesAux acc).drop (4 * j) = b0 :: b1 :: b2 :: b3 :: rest
  | .empty, _, _, _, _, hget => by simp [WordTree.getQuad?] at hget
  | .leaf b0' b1' b2' b3', _, acc, 0, _, hget => by
    simp only [WordTree.getQuad?, Option.some.injEq, Prod.mk.injEq] at hget
    rcases hget with ⟨rfl, rfl, ⟨rfl, rfl⟩⟩
    exact ⟨acc, rfl⟩
  | .leaf _ _ _ _, _, _, _ + 1, _, hget => by simp [WordTree.getQuad?] at hget
  | .node lw l r, _, acc, j, hsz, hget => by
    simp only [WordTree.checkSize?] at hsz
    split at hsz <;> try contradiction
    rename_i nl nr hl hr
    split at hsz <;> try contradiction
    rename_i hlw
    have hlw_eq : lw = nl := beq_iff_eq.mp hlw
    subst hlw_eq
    simp only [WordTree.getQuad?] at hget
    split at hget
    · exact getQuad?_drop_toBytesAux' l (r.toBytesAux acc) j hl hget
    · have hj : 4 * j = 4 * lw + 4 * (j - lw) := by omega
      rw [WordTree.toBytesAux, hj, ← List.drop_drop, drop_all_toBytesAux' l (r.toBytesAux acc) hl]
      exact getQuad?_drop_toBytesAux' r acc (j - lw) hr hget

/-- Every offset in `os` is word-aligned and holds the zero word of `t`. -/
def zeroWordsAt (t : WordTree) : List Nat → Bool
  | [] => true
  | o :: os => (o % 4 == 0 && decide (t.getQuad? (o / 4) = some (0, 0, 0, 0))) && zeroWordsAt t os

theorem zeroWordsAt_mem {t : WordTree} {os : List Nat} (h : zeroWordsAt t os = true) {o : Nat}
    (ho : o ∈ os) : o % 4 = 0 ∧ t.getQuad? (o / 4) = some (0, 0, 0, 0) := by
  induction os with
  | nil => cases ho
  | cons o' os ih =>
    simp only [zeroWordsAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    rcases List.mem_cons.1 ho with rfl | ho
    · exact h.1
    · exact ih h.2 ho

theorem mem_toStringSymbols {l : List (List Char × Nat)} {n : String} {o : Nat}
    (h : (n, o) ∈ toStringSymbols l) : o ∈ l.map (·.2) := by
  induction l with
  | nil => cases h
  | cons hd tl ih =>
    obtain ⟨cs, a⟩ := hd
    simp only [toStringSymbols, List.mem_cons, Prod.mk.injEq, List.map_cons] at h ⊢
    rcases h with ⟨_, rfl⟩ | h
    · exact Or.inl rfl
    · exact Or.inr (ih h)

/-- Kernel check: every stub of the session image sits on a zero word. -/
theorem libsignalSessionCode_stubsZero :
    zeroWordsAt libsignalSessionCode_tree (libsignalSessionCode_stubChars.map (·.2)) = true := by
  rfl_kernel

theorem decode_zero : decode (0#8 ++ 0#8 ++ 0#8 ++ 0#8) = none := by rfl_kernel

theorem libsignalSessionCode_readWordOff_zero {o : Nat} (ho : o % 4 = 0)
    (hq : libsignalSessionCode_tree.getQuad? (o / 4) = some (0, 0, 0, 0)) :
    libsignalSessionCode.readWordOff o = some (0#8 ++ 0#8 ++ 0#8 ++ 0#8) := by
  obtain ⟨rest, hdrop⟩ :=
    getQuad?_drop_toBytesAux' libsignalSessionCode_tree [] (o / 4) libsignalSessionCode_tree_size hq
  have ho4 : o = 4 * (o / 4) := by omega
  unfold Program.readWordOff
  rw [libsignalSessionCode_code_eq, WordTree.toBytes]
  have hal : ¬(o % 4 ≠ 0) := by omega
  simp only [hal, ↓reduceIte]
  rw [ho4, hdrop]
  rfl

/-- No stub word of the session image decodes. -/
theorem libsignalSessionCode_stubsDead : StubsDead libsignalSessionCode := by
  intro n o hmem
  rw [libsignalSessionCode_stubs_eq] at hmem
  obtain ⟨ho, hq⟩ := zeroWordsAt_mem libsignalSessionCode_stubsZero (mem_toStringSymbols hmem)
  exact ⟨_, libsignalSessionCode_readWordOff_zero ho hq, decode_zero⟩

/-- `sessionExterns F alloc` maps the three allocator symbol names to `alloc`'s hooks. -/
theorem sessionExterns_alloc (F : CryptoGames.HMAC.ShaState → List (BitVec 8) → CryptoGames.HMAC.ShaState)
    (alloc : String → Option (State → State)) :
    ["__rustc::__rust_alloc", "__rustc::__rust_dealloc", "__rustc::__rust_realloc"].map
        (CryptoVerification.LibsignalSession.sessionExterns F alloc) =
      [alloc "__rustc::__rust_alloc", alloc "__rustc::__rust_dealloc",
        alloc "__rustc::__rust_realloc"] := by
  rfl_kernel

/-- `sessionExterns F alloc` does not depend on `alloc` outside the three allocator names. -/
theorem sessionExterns_not_alloc {F : CryptoGames.HMAC.ShaState → List (BitVec 8) → CryptoGames.HMAC.ShaState}
    {a1 a2 : String → Option (State → State)} {n : String}
    (hn : ¬(n = "__rustc::__rust_alloc" ∨ n = "__rustc::__rust_dealloc" ∨
      n = "__rustc::__rust_realloc")) :
    CryptoVerification.LibsignalSession.sessionExterns F a1 n =
      CryptoVerification.LibsignalSession.sessionExterns F a2 n := by
  unfold CryptoVerification.LibsignalSession.sessionExterns
  simp only [hn, ↓reduceIte]

/-- `tripleRatchetExterns C ctl abs` maps the three allocator symbol names to `abs`'s hooks. -/
theorem tripleRatchetExterns_alloc (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    ["__rustc::__rust_alloc", "__rustc::__rust_dealloc", "__rustc::__rust_realloc"].map
        (tripleRatchetExterns C ctl abs) =
      [abs "__rustc::__rust_alloc", abs "__rustc::__rust_dealloc",
        abs "__rustc::__rust_realloc"] := by
  rfl_kernel

/-- `Rust.withPanics (sessionExterns C.F abs)` is pointwise ≤
`Rust.withPanics (tripleRatchetExterns C ctl abs)`. -/
theorem sessionExterns_le (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    ∀ n f, Rust.withPanics (CryptoVerification.LibsignalSession.sessionExterns C.F abs) n = some f →
      Rust.withPanics (tripleRatchetExterns C ctl abs) n = some f := by
  apply withPanics_mono
  intro n f h
  by_cases hn : n = "__rustc::__rust_alloc" ∨ n = "__rustc::__rust_dealloc" ∨
      n = "__rustc::__rust_realloc"
  · have h1 := sessionExterns_alloc C.F abs
    have h2 := tripleRatchetExterns_alloc C ctl abs
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at h1 h2
    rcases hn with rfl | rfl | rfl
    · rw [h1.1] at h; rw [h2.1]; exact h
    · rw [h1.2.1] at h; rw [h2.2.1]; exact h
    · rw [h1.2.2.1] at h; rw [h2.2.2.1]; exact h
  · have e := sessionExterns_not_alloc (F := C.F) (a1 := abs) (a2 := fun _ => none) hn
    unfold tripleRatchetExterns
    rw [← e, h]

theorem sessionExterns_le_trap (C : Crypto)
    (abs : String → Option (State → State)) :
    ∀ n f, Rust.withPanics (CryptoVerification.LibsignalSession.sessionExterns C.F abs) n = some f →
      Rust.withPanics (trTrapExterns C abs) n = some f := by
  intro n f h
  by_cases hr : n = rngFillName
  · subst hr
    by_cases hp : Rust.isPanicSymbol rngFillName = true
    · simp [Rust.withPanics, hp] at h ⊢; exact h
    · simp [Rust.withPanics, hp, CryptoVerification.LibsignalSession.sessionExterns, rngFillName] at h
  · rw [withPanics_trTrap_ne C abs hr]
    exact sessionExterns_le C 0#64 abs n f h

theorem session_subroutine_ok_mono_trap {α : Type} {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img) {C : Crypto}
    {abs : String → Option (State → State)}
    {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok (CryptoVerification.LibsignalSession.sessionProg img C.F abs) entry spec) :
    subroutine_ok (trTrapProgAt img.base C abs) entry spec := by
  have e : CryptoVerification.LibsignalSession.sessionProg img C.F abs =
      libsignalSessionCode.rebase img.base
        (Rust.withPanics (CryptoVerification.LibsignalSession.sessionExterns C.F abs)) :=
    libsignalSessionCode_ofImage himg
  rw [e] at h
  exact subroutine_ok_rebase_mono libsignalSessionCode_stubs_offsets_fresh
    libsignalSessionCode_stubsDead (sessionExterns_le_trap C abs) h

/-- A `subroutine_ok` contract proved on `sessionProg img C.F abs` holds on
`tripleRatchetProgAt img.base C ctl abs`. -/
theorem session_subroutine_ok_mono {α : Type} {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img) {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok (CryptoVerification.LibsignalSession.sessionProg img C.F abs) entry spec) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs) entry spec :=
  subroutine_ok_kit_of_trTrap (session_subroutine_ok_mono_trap himg h)

/-- Transfers a `sessionProg img F abs` `subroutine_ok` contract to any hook map `ext` extending
`Rust.withPanics (sessionExterns F abs)`. -/
theorem session_subroutine_ok_mono_ext {α : Type} {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {F : CryptoGames.HMAC.ShaState → List (BitVec 8) → CryptoGames.HMAC.ShaState}
    {abs ext : String → Option (State → State)}
    (hle : ∀ n f, Rust.withPanics (CryptoVerification.LibsignalSession.sessionExterns F abs) n = some f →
      Rust.withPanics ext n = some f)
    {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok (CryptoVerification.LibsignalSession.sessionProg img F abs) entry spec) :
    subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) entry spec := by
  have e : CryptoVerification.LibsignalSession.sessionProg img F abs =
      libsignalSessionCode.rebase img.base
        (Rust.withPanics (CryptoVerification.LibsignalSession.sessionExterns F abs)) :=
    libsignalSessionCode_ofImage himg
  rw [e] at h
  exact subroutine_ok_rebase_mono libsignalSessionCode_stubs_offsets_fresh
    libsignalSessionCode_stubsDead hle h

/-! ## Relocatable `[LibsignalPlacement]` Block Transfer Helpers -/

/-- Transfer a `withLsCodeLoaded lsmpl spec` contract proved on `calleeProg` (block `j`) to any
`callerProg` (block `i`) sharing the same hook map `H`. -/
theorem ls_subroutine_ok_transfer [LibsignalPlacement] {α : Type}
    {callerProg calleeProg : Program} {i j : Nat}
    {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok calleeProg entry (withLsCodeLoaded lsmpl spec))
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCodeLoaded lsmpl spec) :=
  ls_subroutine_ok_of_block (callerProg := callerProg) (calleeProg := calleeProg) h hi hj hj_unmut

/-- Transfer an unaugmented `spec` contract proved on `calleeProg` (block `j`) to any
`callerProg` (block `i`) sharing `H`, wrapping in `withLsCodeLoaded lsmpl`. -/
theorem ls_subroutine_ok_transfer_of_plain [LibsignalPlacement] {α : Type}
    {callerProg calleeProg : Program} {i j : Nat}
    {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok calleeProg entry spec)
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCodeLoaded lsmpl spec) :=
  ls_subroutine_ok_transfer (subroutine_ok_withLsCodeLoaded_of_plain h) hi hj hj_unmut

end CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer

