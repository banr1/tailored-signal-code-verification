/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Legacy.Spec.Library
public import Arm64.Legacy.Spec.Helpers
public import ProofLib.ObjectLoad
public import ProofLib.Invariant
import ProofLib.SepLogic.Model
import ProofLib.Hoare.Model

/-!
# Compositional Library Verification

Compositional-linking lemmas for `LibrarySpec`, `LinksIn`, and `library_ok`: dependency-closure
transitivity, `LinksIn` monotonicity, trusted-dependency elimination (`library_ok.discharge`),
and contract lifting for relocation-free object functions (`Contract.Holds.of_relocFreeFn`).
-/

@[expose] public section

namespace Arm64

namespace LibrarySpec

theorem mem_closure_go_iff {deps : List LibrarySpec} {x : LibrarySpec} :
    x ∈ closure.go deps ↔ ∃ D ∈ deps, x ∈ D.closure := by
  induction deps with
  | nil =>
    simp [closure.go]
  | cons D rest ih =>
    simp only [closure.go, List.mem_append, ih, List.mem_cons, exists_eq_or_imp]

theorem mem_closure_iff {L x : LibrarySpec} :
    x ∈ L.closure ↔ (∃ D ∈ L.deps, x ∈ D.closure) ∨ x = L := by
  rcases L with ⟨name, obj, deps, contracts⟩
  simp [closure, mem_closure_go_iff]

theorem self_mem_closure (L : LibrarySpec) : L ∈ L.closure :=
  mem_closure_iff.2 (Or.inr rfl)

theorem closure_trans : ∀ (A : LibrarySpec) {B x : LibrarySpec},
    B ∈ A.closure → x ∈ B.closure → x ∈ A.closure
  | ⟨name, obj, deps, contracts⟩, B, x, hB, hx => by
    let rec go : (ds : List LibrarySpec) → B ∈ closure.go ds → x ∈ closure.go ds
      | [], h => by simp [closure.go] at h
      | D :: rest, h => by
        simp only [closure.go, List.mem_append] at h ⊢
        rcases h with h1 | h2
        · exact Or.inl (closure_trans D h1 hx)
        · exact Or.inr (go rest h2)
    simp only [closure, List.mem_append, List.mem_singleton] at hB
    rcases hB with h1 | rfl
    · simp only [closure, List.mem_append, List.mem_singleton]
      exact Or.inl (go deps h1)
    · exact hx

end LibrarySpec

theorem LinksIn.mono {specs₁ specs₂ : List LibrarySpec} {img : Obj.Image}
    {trusted₁ trusted₂ : List LibrarySpec}
    (h : LinksIn specs₁ img trusted₁)
    (hspecs : ∀ D ∈ specs₂, D ∈ specs₁ ∧ (D ∈ trusted₁ → D ∈ trusted₂)) :
    LinksIn specs₂ img trusted₂ := by
  obtain ⟨li, hpres, hloads⟩ := h
  refine ⟨li, fun D hD => ?_, hloads⟩
  obtain ⟨hD₁, hT⟩ := hspecs D hD
  rcases hpres D hD₁ with hl | ⟨hDt, hx⟩
  · exact Or.inl hl
  · exact Or.inr ⟨hT hDt, hx⟩

/-- A library outside `trusted` has its object linked in. -/
theorem LinksIn.objectLoaded {specs trusted : List LibrarySpec} {li : Obj.LinkedImage}
    (h : ∀ D ∈ specs, D.ObjectLoaded li ∨ (D ∈ trusted ∧ D.ProvidedAsExterns li))
    {D : LibrarySpec} (hD : D ∈ specs) (hDT : D ∉ trusted) {o : Obj.ObjectInfo}
    (ho : D.obj = some o) : o ∈ li.objects := by
  rcases h D hD with hl | ⟨hDt, _⟩
  · exact hl o ho
  · exact absurd hDt hDT

/-- Discharge a trusted library: if `A` holds trusting `B :: T`, `B` holds trusting `T`,
    and `B ∈ A.closure`, then `A` holds trusting only `T`. -/
theorem library_ok.discharge {A B : LibrarySpec} {T : List LibrarySpec}
    (hA : library_ok A (B :: T)) (hB : library_ok B T) (hBdep : B ∈ A.closure) :
    library_ok A T := by
  refine ⟨fun D hD hDT => ?_, fun img X hLinks hTrusted D hD hDT c hc => ?_⟩
  · by_cases hDB : D = B
    · subst hDB
      exact hB.1 D D.self_mem_closure hDT
    · exact hA.1 D hD (by simp [hDB, hDT])
  · have hLinksB : LinksIn B.closure img T :=
      hLinks.mono fun D' hD' => ⟨A.closure_trans hBdep hD', id⟩
    have hTrustedB : TrustedLibrariesOK T img X B.closure :=
      fun D' hD' hD'T => hTrusted D' (A.closure_trans hBdep hD') hD'T
    by_cases hDB : D = B
    · subst hDB
      exact hB.2 img X hLinksB hTrustedB D D.self_mem_closure hDT c hc
    · have hLinksA : LinksIn A.closure img (B :: T) :=
        hLinks.mono fun D' hD' => ⟨hD', List.mem_cons_of_mem B⟩
      have hTrustedBT : TrustedLibrariesOK (B :: T) img X A.closure := by
        intro D' hD' hD'BT c' hc' a ha
        rcases List.mem_cons.1 hD'BT with rfl | hD'T
        · by_cases hBT : D' ∈ T
          · exact hTrusted D' hBdep hBT c' hc' a ha
          · obtain ⟨a₀, ha₀, hsub⟩ := hB.2 img X hLinksB hTrustedB D' D'.self_mem_closure hBT c' hc'
            rw [ha] at ha₀
            cases ha₀
            exact hsub
        · exact hTrusted D' hD' hD'T c' hc' a ha
      exact hA.2 img X hLinksA hTrustedBT D hD (by simp [hDB, hDT]) c hc

/-- Any `subroutine_ok` proof for `spec` weakens to `spec.inImage img`, which only strengthens
    the precondition with `img.FrozenLoaded s0 ∧ s0.symtab = img.symtab`. -/
theorem subroutine_ok_inImage {α : Type} {prog : Program} {entry_pc : BitVec 64}
    {spec : Spec α} (img : Obj.Image) (h : subroutine_ok prog entry_pc spec) :
    subroutine_ok prog entry_pc (spec.inImage img) := by
  simp only [subroutine_ok_iff, reaches_outcome_iff] at h ⊢
  intro x R s0 hpc hrun hpre hsp
  simp only [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact h x R s0 hpc hrun hpre.2 hsp

/-- Establish `library_ok L` when `L.deps = []` and `L.obj = some o`. -/
theorem library_ok_single {L : LibrarySpec} {o : Obj.ObjectInfo}
    (hdeps : L.deps = []) (hobj : L.obj = some o)
    (hcontracts : ∀ (img : Obj.Image) (X : String → Option (State → State)),
      (∃ li : Obj.LinkedImage, o ∈ li.objects ∧ Obj.Loads li img) →
      ∀ c ∈ L.contracts, Contract.Holds L img X c) :
    library_ok L := by
  have hclosure : L.closure = [L] := by
    rcases L with ⟨name, obj, deps, contracts⟩
    cases hdeps
    rfl
  refine ⟨fun D hD _ => ?_, fun img X hLinks _ D hD _ c hc => ?_⟩
  · rw [hclosure, List.mem_singleton] at hD
    subst hD
    simp [hobj]
  · rw [hclosure, List.mem_singleton] at hD
    subst hD
    obtain ⟨li, hmem, hloads⟩ := hLinks
    have ho : o ∈ li.objects := LinksIn.objectLoaded hmem
      (by rw [hclosure]; exact List.mem_singleton_self _) List.not_mem_nil hobj
    exact hcontracts img X ⟨li, ho, hloads⟩ c hc

/-! ## Program equivalence under replacing `symbols` when `overrides = fun _ => none` -/

namespace Program

theorem findSome?_overrides_none (syms : List (String × Nat)) (off : Nat) :
    (syms.findSome? fun (_n, o) => if o == off then (none : Option (State → State)) else none) = none := by
  simp

theorem hookAtOff?_with_symbols (prog : Program) (hO : prog.overrides = fun _ => none)
    (syms : List (String × Nat)) (off : Nat) :
    ({ prog with symbols := syms }).hookAtOff? off = prog.hookAtOff? off := by
  simp only [hookAtOff?, hO, findSome?_overrides_none]

theorem externAt?_with_symbols (prog : Program) (hO : prog.overrides = fun _ => none)
    (syms : List (String × Nat)) (pc : BitVec 64) :
    ({ prog with symbols := syms }).externAt? pc = prog.externAt? pc :=
  hookAtOff?_with_symbols prog hO syms _

theorem fetchMem_with_symbols (prog : Program) (hO : prog.overrides = fun _ => none)
    (syms : List (String × Nat)) (m : Memory) (pc : BitVec 64) :
    ({ prog with symbols := syms }).fetchMem m pc = prog.fetchMem m pc := by
  simp only [fetchMem, externAt?_with_symbols prog hO syms]

theorem step_with_symbols_iff (prog : Program) (hO : prog.overrides = fun _ => none)
    (syms : List (String × Nat)) (s s' : State) :
    Step { prog with symbols := syms } s s' ↔ Step prog s s' := by
  constructor <;> intro h <;> cases h with
  | exec hr hf =>
    exact Step.exec hr (by simpa [fetchMem_with_symbols prog hO syms] using hf)
  | halt_unmapped hr hf he =>
    exact Step.halt_unmapped hr
      (by simpa [fetchMem_with_symbols prog hO syms] using hf)
      (by simpa [externAt?_with_symbols prog hO syms] using he)
  | extern hr he hk hs =>
    exact Step.extern hr (by simpa [externAt?_with_symbols prog hO syms] using he) hk hs
  | extern_fault hr he hnk =>
    exact Step.extern_fault hr (by simpa [externAt?_with_symbols prog hO syms] using he) hnk

theorem steps_with_symbols_iff (prog : Program) (hO : prog.overrides = fun _ => none)
    (syms : List (String × Nat)) {s s' : State} :
    Steps { prog with symbols := syms } s s' ↔ Steps prog s s' := by
  constructor <;> intro h <;> induction h with
  | refl s => exact Steps.refl s
  | step h1 _ ih =>
    first
      | exact Steps.step ((step_with_symbols_iff prog hO syms _ _).1 h1) ih
      | exact Steps.step ((step_with_symbols_iff prog hO syms _ _).2 h1) ih

theorem subroutine_ok_of_with_symbols {α : Type} (prog : Program)
    (hO : prog.overrides = fun _ => none) (sym : String) (off : Nat) (spec : Spec α)
    (h : ({ prog with symbols := [(sym, off)] }).subroutineOk sym spec) :
    subroutine_ok prog (prog.base + BitVec.ofNat 64 off) spec := by
  have hfnAddr : ({ prog with symbols := [(sym, off)] }).fnAddr sym =
      prog.base + BitVec.ofNat 64 off := by
    simp [fnAddr, fnOff, findSymbol?]
  simp only [subroutine_ok_iff, reaches_outcome_iff] at h ⊢
  intro x R s0 hpc hrun hpre hsp hcode
  obtain ⟨sf, hsteps, hpost⟩ :=
    h x R s0 (hpc.trans hfnAddr.symm) hrun hpre hsp (hcode.of_base_code rfl rfl)
  exact ⟨sf, (steps_with_symbols_iff prog hO _).1 hsteps, hpost⟩

end Program

/-! ## Relocation-free functions recorded by the linker -/

namespace Obj

theorem lookup_mem {α : Type} {name : String} {xs : List (String × α)} {v : α}
    (h : lookup name xs = some v) : (name, v) ∈ xs := by
  unfold lookup at h
  cases hf : xs.find? (·.1 == name) with
  | none => simp [hf] at h
  | some p =>
    rw [hf] at h
    cases h
    have hmem := List.mem_of_find?_eq_some hf
    have hn : p.1 = name := by simpa using List.find?_some hf
    obtain ⟨n, v'⟩ := p
    simp only at hn
    subst hn
    exact hmem

theorem LinkedImage.wellFormed_objects {li : LinkedImage} (h : li.wellFormed = true) :
    ∀ o ∈ li.objects, li.honours o = true := by
  unfold LinkedImage.wellFormed at h
  simp only [Bool.and_eq_true] at h
  exact List.all_eq_true.1 h.2

theorem LinkedImage.wellFormed_code_le {li : LinkedImage} (h : li.wellFormed = true) :
    li.code.length ≤ li.gotOff := by
  unfold LinkedImage.wellFormed at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, _⟩, h3⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := h
  unfold LinkedImage.dataEnd at h3
  omega

theorem LinkedImage.honours_fn {li : LinkedImage} {o : ObjectInfo} (h : li.honours o = true)
    {f : String} {bs : List (BitVec 8)} (hf : (f, bs) ∈ o.fns) :
    ∃ syms off, lookup o.name li.objSymbols = some syms ∧ lookupUnique f syms = some off ∧
      off % 4 = 0 ∧ off + bs.length ≤ li.code.length ∧ (li.code.drop off).take bs.length = bs ∧
      ∀ s ∈ li.stubs, ¬(off ≤ s.2 ∧ s.2 < off + bs.length) := by
  unfold LinkedImage.honours at h
  split at h
  · contradiction
  rename_i syms hsyms
  simp only [Bool.and_eq_true] at h
  have hfn := List.all_eq_true.1 h.1.1.1 _ hf
  simp only at hfn
  split at hfn
  · contradiction
  rename_i off hoff
  simp only [Bool.and_eq_true, beq_iff_eq, bytesAt, decide_eq_true_eq, List.all_eq_true] at hfn
  obtain ⟨⟨⟨_hsym, hal⟩, hlen, hbytes⟩, hstubs⟩ := hfn
  exact ⟨syms, off, hsyms, hoff, hal, hlen, hbytes, fun s hs => by have := hstubs s hs; simp at this; omega⟩

theorem LinkedImage.honours_fn_sym {li : LinkedImage} {o : ObjectInfo} (h : li.honours o = true)
    {f : String} {bs : List (BitVec 8)} (hf : (f, bs) ∈ o.fns) :
    ∃ syms off, lookup o.name li.objSymbols = some syms ∧ lookupUnique f syms = some off ∧
      lookup f li.symbols = some off := by
  unfold LinkedImage.honours at h
  split at h
  · contradiction
  rename_i syms hsyms
  simp only [Bool.and_eq_true] at h
  have hfn := List.all_eq_true.1 h.1.1.1 _ hf
  simp only at hfn
  split at hfn
  · contradiction
  rename_i off hoff
  simp only [Bool.and_eq_true, beq_iff_eq] at hfn
  obtain ⟨⟨⟨hsym, _⟩, _⟩, _⟩ := hfn
  exact ⟨syms, off, hsyms, hoff, hsym⟩

theorem take4_drop_of_drop_take {α : Type} {xs ys : List α} {secOff k : Nat}
    (h : (xs.drop secOff).take ys.length = ys) (hk : k + 4 ≤ ys.length) :
    (xs.drop (secOff + k)).take 4 = (ys.drop k).take 4 := by
  rw [← h, List.drop_take, List.drop_drop, List.take_take, Nat.min_eq_left (by omega)]

theorem readWordOff_eq_of_take4 {prog1 prog2 : Program} {k1 k2 : Nat}
    (hal1 : k1 % 4 = 0) (hal2 : k2 % 4 = 0)
    (htake : (prog1.code.drop k1).take 4 = (prog2.code.drop k2).take 4) :
    prog1.readWordOff k1 = prog2.readWordOff k2 := by
  simp only [Program.readWordOff, hal1, hal2, ne_eq, not_true_eq_false, ↓reduceIte]
  revert htake
  rcases prog1.code.drop k1 with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _⟩⟩⟩⟩ <;>
  rcases prog2.code.drop k2 with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _⟩⟩⟩⟩ <;>
  simp
  rintro rfl rfl rfl rfl; rfl

theorem readWordOff_of_slice {prog : Program} {secBytes : List (BitVec 8)} {secOff k : Nat}
    (hslice : (prog.code.drop secOff).take secBytes.length = secBytes)
    (hsec_al : secOff % 4 = 0) (hk_al : k % 4 = 0) (hk_len : k + 4 ≤ secBytes.length) :
    prog.readWordOff (secOff + k) = ({ code := secBytes } : Program).readWordOff k :=
  readWordOff_eq_of_take4 (by omega) hk_al (take4_drop_of_drop_take hslice hk_len)

end Obj

theorem checkBytesWordsBound_length_le {rem : Nat} {bs : List (BitVec 8)} {words : List (BitVec 32)}
    (h : Program.checkBytesWordsBound rem bs words = true) :
    4 * words.length ≤ bs.length := by
  induction words generalizing rem bs with
  | nil => simp
  | cons w ws ih =>
    match bs with
    | [] | [_] | [_, _] | [_, _, _] => simp [Program.checkBytesWordsBound] at h
    | b0 :: b1 :: b2 :: b3 :: rest =>
      simp only [Program.checkBytesWordsBound, Bool.and_eq_true, decide_eq_true_eq] at h
      have h_ih := ih h.2
      simp only [List.length_cons]
      omega

theorem checkBytesWordsBound_hasWordsOff_zero {bs : List (BitVec 8)} {words : List (BitVec 32)}
    (h : Program.checkBytesWordsBound (2 ^ 64) bs words = true) :
    4 * words.length ≤ bs.length ∧ ({ code := bs } : Program).hasWordsOff 0 words := by
  refine ⟨checkBytesWordsBound_length_le h, ?_⟩
  apply Program.hasWordsOff_of_checkBytesWordsBound (by rfl) (by omega)
  simp only [Nat.sub_zero, List.drop_zero, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨rfl, rfl⟩, h⟩

/-- Decidable linear-time check that the linker recorded function `symName` of `o` with bytes
    that begin with the 32-bit instruction words `hex`. -/
def checkRelocFreeFn (o : Obj.ObjectInfo) (symName : String) (hex : List (BitVec 32)) : Bool :=
  match Obj.lookup symName o.fns with
  | some bs => Program.checkBytesWordsBound (2 ^ 64) bs hex
  | none => false

/-- Layout-generic contract verification for a relocation-free function:
    If `D.obj = some o`, `o` is recorded in the linked image of `img`,
    `checkRelocFreeFn o c.sym hex = true`, and `h_ok` proves `prog.subroutineOk c.sym c.spec`
    for any `prog` with `prog.codeAt c.sym hex`, then `Contract.Holds D img X c` holds. -/
theorem Contract.Holds.of_relocFreeFn
    {D : LibrarySpec} {o : Obj.ObjectInfo} {img : Obj.Image}
    {X : String → Option (State → State)} {c : Contract} {hex : List (BitVec 32)}
    (hD : D.obj = some o)
    (hLoads : ∃ li : Obj.LinkedImage, o ∈ li.objects ∧ Obj.Loads li img)
    (hcheck : checkRelocFreeFn o c.sym hex = true)
    (h_ok : ∀ prog : Program, prog.codeAt c.sym hex → prog.subroutineOk c.sym c.spec) :
    Contract.Holds D img X c := by
  unfold checkRelocFreeFn at hcheck
  split at hcheck
  case h_2 => contradiction
  rename_i bs hbs
  obtain ⟨hlen, hwords⟩ := checkBytesWordsBound_hasWordsOff_zero hcheck
  obtain ⟨li, ho, hloads⟩ := hLoads
  obtain ⟨_, _, _, hwf, hwrap, _⟩ := ProofLib.ObjectLoad.load_eq_ok hloads
  obtain ⟨_, hcode, _, hstubsEq, hobjSyms, _, _⟩ := ProofLib.ObjectLoad.load_ok hloads
  obtain ⟨syms, off, hsyms, hoff, hal, hend, hslice, hstubs⟩ :=
    Obj.LinkedImage.honours_fn (Obj.LinkedImage.wellFormed_objects hwf o ho) (Obj.lookup_mem hbs)
  have hcodeLe := Obj.LinkedImage.wellFormed_code_le hwf
  have haddr : D.addr? img c.sym = some (img.base + BitVec.ofNat 64 off) := by
    simp [LibrarySpec.addr?, hD, hobjSyms, hsyms, hoff]
  let prog := Program.ofImage img (Rust.withPanics X)
  let prog' : Program := { prog with symbols := [(c.sym, off)] }
  have hfnOff : prog'.fnOff c.sym = off := by
    simp [prog', Program.fnOff, Program.findSymbol?]
  have hcodeAt : prog'.codeAt c.sym hex := by
    unfold Program.codeAt Program.hasWordsOff
    rw [hfnOff]
    refine ⟨by omega, fun i hi => ?_, ?_⟩
    · have hslice' : (prog'.code.drop off).take bs.length = bs := by
        show (img.code.drop off).take bs.length = bs
        rw [hcode]; exact hslice
      rw [Obj.readWordOff_of_slice hslice' hal (by omega) (by omega)]
      have := hwords.2.1 i hi
      rwa [Nat.zero_add] at this
    · unfold Program.hookFree
      rw [List.all_eq_true, List.all_eq_true]
      refine ⟨?_, ?_⟩
      · rintro ⟨n, stubOff⟩ hstub
        rw [Bool.or_eq_true]
        left
        have hge := hstubs (n, stubOff) (by
          have hstub' : (n, stubOff) ∈ img.stubs := hstub
          rwa [hstubsEq] at hstub')
        simp only [Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq,
          decide_eq_false_iff_not]
        intro _
        simp only at hge
        omega
      · rintro ⟨n, symOff⟩ _
        rw [Bool.or_eq_true]
        right
        rfl
  have hsub' := h_ok prog' hcodeAt
  have hsub := Program.subroutine_ok_of_with_symbols prog rfl c.sym off c.spec hsub'
  exact ⟨img.base + BitVec.ofNat 64 off, haddr, subroutine_ok_inImage img hsub⟩

end Arm64
