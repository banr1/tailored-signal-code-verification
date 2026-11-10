/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Process
public import Arm64.Trusted.Process.Overrides

/-!
# Symbol-Keyed Override Resolution

Proves symbol-to-address hook resolution properties for `overrideProgram` and provides
`fastResolveAddrs` / `checkOverrides` mirrors of `resolveAddrs` that evaluate via
`decide +kernel` on ELF images, supporting `ElfRunsToWithOverrides.intro` and
`ElfRunsToWithOverrides.not_of_check`.
-/

@[expose] public section

namespace Arm64.Process

/-! ## Site programs -/

theorem find?_key_eq_of_mem {α β : Type} [BEq β] [LawfulBEq β] (k : α → β) :
    ∀ {xs : List α} {x : α}, (xs.map k).Nodup → x ∈ xs → xs.find? (k · == k x) = some x
  | [], _, _, hx => absurd hx (List.not_mem_nil)
  | y :: ys, x, hnd, hx => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.find?_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · simp
    · have hne : k y ≠ k x := fun h => hnd.1 (h ▸ List.mem_map_of_mem hx)
      have : (k y == k x) = false := by simpa using hne
      rw [this]
      exact find?_key_eq_of_mem k hnd.2 hx

theorem Program.ofSites_externAt (svc : State → State) (sites : List (String × Nat × (State → State)))
    (hnd : (sites.map (·.1)).Nodup) (pc : BitVec 64) :
    (Program.ofSites svc sites).externAt? pc = (sites.find? (·.2.1 == pc.toNat)).map (·.2.2) := by
  have key : ∀ (O : String → Option (State → State)) (l : List (String × Nat × (State → State))),
      (∀ s ∈ l, O s.1 = some s.2.2) →
      ((l.map fun (n, a, _) => (n, a)).findSome? fun (n, o) => if o == pc.toNat then O n else none) =
        (l.find? (·.2.1 == pc.toNat)).map (·.2.2) := by
    intro O l hO
    induction l with
    | nil => rfl
    | cons s l ih =>
      obtain ⟨n, a, f⟩ := s
      rw [List.map_cons, List.findSome?_cons, List.find?_cons]
      by_cases h : a = pc.toNat
      · subst h
        simp [hO (n, _, f) List.mem_cons_self]
      · have hb : (a == pc.toNat) = false := by simpa using h
        simp only [hb, Bool.false_eq_true, ↓reduceIte]
        exact ih fun s hs => hO s (List.mem_cons_of_mem _ hs)
  unfold Program.externAt? Program.hookAtOff?
  rw [show (Program.ofSites svc sites).base = 0#64 from rfl, BitVec.sub_zero]
  exact key _ sites fun s hs => by
    show (sites.find? (·.1 == s.1)).map (·.2.2) = some s.2.2
    rw [find?_key_eq_of_mem (·.1) hnd hs]
    rfl

/-! ## Resolution -/

/-- Pointwise relation between two lists of equal length (local `Forall₂`). -/
def ListRel {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | x :: xs, y :: ys => R x y ∧ ListRel R xs ys
  | _, _ => False

theorem resolveSym_ok {img : ElfImage} {syms : List ElfSym} {shdrs : List ElfShdr}
    {name : String} {a : Nat} (h : resolveSym img syms shdrs name = .ok a) :
    ∃ e sh, syms.filter (·.name == name) = [e] ∧ shdrs[e.shndx]? = some sh ∧ a = e.value ∧
      e.type = 2 ∧ e.size ≠ 0 ∧ e.value % 4 = 0 ∧ e.shndx ≠ 0 ∧ e.shndx < 0xff00 ∧
      sh.type = 1 ∧ sh.flags &&& 6 = 6 ∧ sh.addr ≤ e.value ∧ e.value + e.size ≤ sh.addr + sh.size ∧
      ∃ r ∈ img.segments, r.perm.x = true ∧ r.start.toNat ≤ e.value ∧
        e.value + e.size ≤ r.start.toNat + r.bytes.length := by
  unfold resolveSym at h
  split at h
  · rename_i e hf
    split at h
    · rename_i sh hsh
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq,
          List.any_eq_true, and_assoc] at hc
        obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, r, hr, hrx, hr1, hr2⟩ := hc
        exact ⟨e, sh, hf, hsh, (Except.ok.inj h).symm, h1, h2, h3, h4, h5, h6, h7, h8, h9,
          r, hr, hrx, hr1, hr2⟩
      · cases h
    · cases h
  · cases h
  · cases h

theorem mapM_except_ok {α β ε : Type} (f : α → Except ε β) :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys → ListRel (fun x y => f x = .ok y) xs ys
  | [], ys, h => by
    cases (Except.ok.inj h : [] = ys); trivial
  | x :: xs, ys, h => by
    rw [List.mapM_cons] at h
    cases hx : f x with
    | error e => rw [hx] at h; cases h
    | ok y =>
      rw [hx] at h
      cases hxs : xs.mapM f with
      | error e => rw [hxs] at h; cases h
      | ok ys' =>
        rw [hxs] at h
        cases (Except.ok.inj h : y :: ys' = ys)
        exact ⟨hx, mapM_except_ok f hxs⟩

theorem resolveAddrs_ok {bytes : List (BitVec 8)} {img : ElfImage} {names : List String}
    {addrs : List Nat} (h : resolveAddrs bytes img names = .ok addrs) :
    ∃ syms shdrs, parseSymtabFull bytes = .ok (syms, shdrs) ∧
      ListRel (fun n a => resolveSym img syms shdrs n = .ok a) names addrs ∧
      names.Nodup ∧ addrs.Nodup := by
  unfold resolveAddrs at h
  cases hp : parseSymtabFull bytes with
  | error e => rw [hp] at h; cases h
  | ok p =>
    obtain ⟨syms, shdrs⟩ := p
    rw [hp] at h
    change (do
      let addrs ← names.mapM (resolveSym img syms shdrs)
      if names.Nodup ∧ addrs.Nodup then pure addrs
      else (Except.error "overrides: duplicate name or address" : Except String (List Nat))) =
        .ok addrs at h
    cases hm : names.mapM (resolveSym img syms shdrs) with
    | error e => rw [hm] at h; cases h
    | ok as =>
      rw [hm] at h
      change (if names.Nodup ∧ as.Nodup then pure as else _) = _ at h
      split at h
      · rename_i hnd
        cases (Except.ok.inj h : as = addrs)
        exact ⟨syms, shdrs, rfl, mapM_except_ok _ hm, hnd.1, hnd.2⟩
      · cases h

/-! ## Override programs -/

def zipSites (os : List (String × (State → State))) (addrs : List Nat) :
    List (String × Nat × (State → State)) :=
  os.zipWith (fun (n, f) a => (n, a, f)) addrs

theorem zipSites_spec {R : String → Nat → Prop} :
    ∀ {os : List (String × (State → State))} {addrs : List Nat},
      ListRel R (os.map (·.1)) addrs →
      (zipSites os addrs).map (·.1) = os.map (·.1) ∧ (zipSites os addrs).map (·.2.1) = addrs ∧
      (∀ s ∈ zipSites os addrs, (s.1, s.2.2) ∈ os ∧ R s.1 s.2.1) ∧
      (∀ p ∈ os, ∃ a, (p.1, a, p.2) ∈ zipSites os addrs ∧ R p.1 a)
  | [], [], _ => by simp [zipSites]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | (n, f) :: os, a :: addrs, ⟨hr, hrest⟩ => by
    obtain ⟨h1, h2, h3, h4⟩ := zipSites_spec hrest
    simp only [zipSites, List.zipWith_cons_cons] at h1 h2 h3 h4 ⊢
    refine ⟨by simp [h1], by simp [h2], ?_, ?_⟩
    · intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact ⟨List.mem_cons_self, hr⟩
      · exact ⟨List.mem_cons_of_mem _ (h3 s hs).1, (h3 s hs).2⟩
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨a, List.mem_cons_self, hr⟩
      · obtain ⟨a', ha', hr'⟩ := h4 p hp
        exact ⟨a', List.mem_cons_of_mem _ ha', hr'⟩

/-- After a successful `resolveAddrs`, the override program has hook `g` at `pc` exactly when
    some override `(n, g) ∈ os` names a function that resolves (unique `.symtab` entry,
    `resolveSym_ok`) to address `pc.toNat`. -/
theorem overrideProgram_externAt_iff {bytes : List (BitVec 8)} {img : ElfImage}
    {svc : State → State} {os : List (String × (State → State))} {addrs : List Nat}
    (h : resolveAddrs bytes img (os.map (·.1)) = .ok addrs) (pc : BitVec 64)
    (g : State → State) :
    (overrideProgram svc os addrs).externAt? pc = some g ↔
      ∃ syms shdrs, parseSymtabFull bytes = .ok (syms, shdrs) ∧
        ∃ n, (n, g) ∈ os ∧ resolveSym img syms shdrs n = .ok pc.toNat := by
  obtain ⟨syms, shdrs, hp, hR, hnn, hna⟩ := resolveAddrs_ok h
  obtain ⟨h1, h2, h3, h4⟩ := zipSites_spec hR
  change (Program.ofSites svc (zipSites os addrs)).externAt? pc = some g ↔ _
  rw [Program.ofSites_externAt _ _ (h1 ▸ hnn)]
  constructor
  · intro hf
    obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp hf
    have hpc' := List.find?_some hs
    have hpc : s.2.1 = pc.toNat := beq_iff_eq.mp hpc'
    obtain ⟨hmem, hr⟩ := h3 s (List.mem_of_find?_eq_some hs)
    exact ⟨syms, shdrs, hp, s.1, hmem, hpc ▸ hr⟩
  · rintro ⟨syms', shdrs', hp', n, hmem, hr⟩
    rw [hp] at hp'
    cases hp'
    obtain ⟨a, ha, hra⟩ := h4 (n, g) hmem
    have : a = pc.toNat := Except.ok.inj (hra.symm.trans hr)
    subst this
    have hna' : ((zipSites os addrs).map (·.2.1)).Nodup := by rw [h2]; exact hna
    rw [find?_key_eq_of_mem (·.2.1) hna' ha]
    rfl

/-- After a successful `resolveAddrs`, the override program has no hook at any `pc` whose
    address is not one of the resolved addresses. -/
theorem overrideProgram_externAt_none {bytes : List (BitVec 8)} {img : ElfImage}
    {svc : State → State} {os : List (String × (State → State))} {addrs : List Nat}
    (h : resolveAddrs bytes img (os.map (·.1)) = .ok addrs) {pc : BitVec 64}
    (hpc : pc.toNat ∉ addrs) :
    (overrideProgram svc os addrs).externAt? pc = none := by
  obtain ⟨syms, shdrs, hp, hR, hnn, hna⟩ := resolveAddrs_ok h
  obtain ⟨h1, h2, h3, h4⟩ := zipSites_spec hR
  change (Program.ofSites svc (zipSites os addrs)).externAt? pc = none
  rw [Program.ofSites_externAt _ _ (h1 ▸ hnn), Option.map_eq_none_iff, List.find?_eq_none]
  intro s hs heq
  exact hpc (h2 ▸ (beq_iff_eq.mp heq ▸ List.mem_map_of_mem hs))

/-! ## Kernel-speed checker -/

def fastParseSymEntries (strtab : List (BitVec 8)) (strSize : Nat) (tree : StrtabTree) :
    Nat → List (BitVec 8) → Except String (List ElfSym)
  | 0, _ => .ok []
  | n + 1, sym =>
    withForcedList (drop24 sym) fun nextSym => do
      let stName := listReadU32LE sym 0
      if stName ≥ strSize then .error "symtab: st_name out of bounds"
      let some name := readStrtabCString (strSize - stName) (lookupStrtabTree strtab stName tree) []
        | .error "symtab: unterminated name"
      let info := listGetByte sym 4
      let e : ElfSym := { name, value := listReadU64LE sym 8, size := listReadU64LE sym 16,
                          type := info % 16, bind := info / 16, shndx := listReadU16LE sym 6 }
      return e :: (← fastParseSymEntries strtab strSize tree n nextSym)

theorem fastParseSymEntries_eq (strtab : List (BitVec 8)) (strSize : Nat) (tree : StrtabTree)
    (htree : tree.Valid strtab) :
    ∀ (n : Nat) (sym : List (BitVec 8)),
      fastParseSymEntries strtab strSize tree n sym = parseSymEntries strtab strSize n sym
  | 0, _ => rfl
  | n + 1, sym => by
    simp only [fastParseSymEntries, parseSymEntries, withForcedList_eq, drop24_eq_drop,
      lookupStrtabTree_eq_drop strtab _ tree htree, fastParseSymEntries_eq strtab strSize tree htree n]
    cases readStrtabCString (strSize - listReadU32LE sym 0) (strtab.drop (listReadU32LE sym 0)) [] <;>
      rfl

theorem fastParseSymEntries_build_eq (strtab : List (BitVec 8)) (strSize d n : Nat)
    (sym : List (BitVec 8)) :
    fastParseSymEntries strtab strSize (buildStrtabTree d 0 strSize strtab) n sym =
      parseSymEntries strtab strSize n sym :=
  fastParseSymEntries_eq strtab strSize _ (buildStrtabTree_valid strtab d 0 strSize strtab rfl) n sym

def fastParseShdrs : Nat → List (BitVec 8) → List ElfShdr
  | 0, _ => []
  | n + 1, sh =>
    withForcedList (drop64 sh) fun next =>
      { type := listReadU32LE sh 4, flags := listReadU64LE sh 8, addr := listReadU64LE sh 16,
        size := listReadU64LE sh 32 } :: fastParseShdrs n next

theorem fastParseShdrs_eq : ∀ (n : Nat) (sh : List (BitVec 8)), fastParseShdrs n sh = parseShdrs n sh
  | 0, _ => rfl
  | n + 1, sh => by
    simp only [fastParseShdrs, parseShdrs, withForcedList_eq, drop64_eq_drop, fastParseShdrs_eq n]

def fastParseSymtabFull (bytes : List (BitVec 8)) : Except String (List ElfSym × List ElfShdr) :=
  withForcedNat (fastFileSize bytes (listReadU64LE bytes 40)) fun fileSize => do
    let eShoff := listReadU64LE bytes 40
    let eShnum := listReadU16LE bytes 60
    if fileSize < 64 || listReadU16LE bytes 58 != 64 || eShnum == 0 then .error "symtab: no shdrs"
    if eShoff + eShnum * 64 > fileSize then .error "symtab: shdrs exceed file"
    withForcedList (fastDrop eShoff bytes) fun shTable => do
      let some (shOff, shSize, shLink, _, shEnt) := fastFindSymtabShdr eShnum shTable
        | .error "symtab: no SHT_SYMTAB"
      if shEnt != 24 || shSize % 24 != 0 || shOff + shSize > fileSize || shLink ≥ eShnum then
        .error "symtab: bad SHT_SYMTAB header"
      let strSh := drop64Blocks shLink shTable
      let strOff := listReadU64LE strSh 24
      let strSize := listReadU64LE strSh 32
      if listReadU32LE strSh 4 != 3 || strOff + strSize > fileSize then
        .error "symtab: bad SHT_STRTAB header"
      withForcedList (fastDrop shOff bytes) fun symtab =>
        withForcedList (fastDrop strOff bytes) fun strtab => do
          let syms ← fastParseSymEntries strtab strSize (buildStrtabTree 6 0 strSize strtab)
            (shSize / 24) symtab
          return (syms, fastParseShdrs eShnum shTable)

theorem fastParseSymtabFull_eq (bytes : List (BitVec 8)) :
    fastParseSymtabFull bytes = parseSymtabFull bytes := by
  simp only [fastParseSymtabFull, parseSymtabFull, withForcedNat_eq, fastFileSize_eq_length,
    withForcedList_eq, fastDrop_eq_drop, fastFindSymtabShdr_eq, drop64Blocks_eq_drop,
    fastParseShdrs_eq, fastParseSymEntries_build_eq]
  cases findSymtabShdr (listReadU16LE bytes 60) (bytes.drop (listReadU64LE bytes 40)) with
  | none => rfl
  | some t => obtain ⟨_, _, _, _, _⟩ := t; rfl

def fastResolveSym (regs : List (Snapshot.Region × Nat)) (syms : List ElfSym)
    (shdrs : List ElfShdr) (name : String) : Except String Nat :=
  match syms.filter (·.name == name) with
  | [e] =>
    match shdrs[e.shndx]? with
    | some sh =>
      if e.type == 2 && e.size != 0 && e.value % 4 == 0 && e.shndx != 0 && e.shndx < 0xff00 &&
          sh.type == 1 && sh.flags &&& 6 == 6 &&
          sh.addr ≤ e.value && e.value + e.size ≤ sh.addr + sh.size &&
          regs.any (fun p => p.1.perm.x && p.1.start.toNat ≤ e.value &&
            e.value + e.size ≤ p.1.start.toNat + p.2) then .ok e.value
      else .error s!"override {name}: not a sized, aligned function in executable code"
    | none => .error s!"override {name}: bad st_shndx"
  | [] => .error s!"override {name}: no .symtab entry"
  | _ => .error s!"override {name}: duplicate .symtab entries"

theorem fastResolveSym_eq (img : ElfImage) (syms : List ElfSym) (shdrs : List ElfShdr)
    (name : String) :
    fastResolveSym (mapRegionsWithLen img.segments) syms shdrs name =
      resolveSym img syms shdrs name := by
  unfold fastResolveSym resolveSym
  simp only [mapRegionsWithLen_eq, List.any_map, Function.comp_def]
  split <;> split <;> first | rfl | simp_all

theorem fastResolveSym_eq' (img : ElfImage) (syms : List ElfSym) (shdrs : List ElfShdr) :
    fastResolveSym (mapRegionsWithLen img.segments) syms shdrs = resolveSym img syms shdrs :=
  funext (fastResolveSym_eq img syms shdrs)

def fastResolveAddrs (bytes : List (BitVec 8)) (img : ElfImage) (names : List String) :
    Except String (List Nat) := do
  let (syms, shdrs) ← fastParseSymtabFull bytes
  let regs := mapRegionsWithLen img.segments
  let addrs ← names.mapM (fastResolveSym regs syms shdrs)
  if names.Nodup ∧ addrs.Nodup then return addrs else .error "overrides: duplicate name or address"

theorem fastResolveAddrs_eq (bytes : List (BitVec 8)) (img : ElfImage) (names : List String) :
    fastResolveAddrs bytes img names = resolveAddrs bytes img names := by
  simp only [fastResolveAddrs, resolveAddrs, fastParseSymtabFull_eq, fastResolveSym_eq']

/-- Boolean checker: `resolveAddrs bytes img names` succeeds with exactly `addrs`. -/
def checkOverrides (bytes : List (BitVec 8)) (img : ElfImage) (names : List String)
    (addrs : List Nat) : Bool :=
  match fastResolveAddrs bytes img names with
  | .ok as => as == addrs
  | .error _ => false

/-- Boolean checker: `resolveAddrs bytes img names` fails. -/
def checkOverridesFail (bytes : List (BitVec 8)) (img : ElfImage) (names : List String) : Bool :=
  match fastResolveAddrs bytes img names with
  | .ok _ => false
  | .error _ => true

theorem resolveAddrs_of_check {bytes : List (BitVec 8)} {img : ElfImage} {names : List String}
    {addrs : List Nat} (h : checkOverrides bytes img names addrs = true) :
    resolveAddrs bytes img names = .ok addrs := by
  rw [← fastResolveAddrs_eq]
  unfold checkOverrides at h
  split at h
  · rename_i as has
    rw [has, beq_iff_eq.mp h]
  · cases h

theorem resolveAddrs_fail_of_check {bytes : List (BitVec 8)} {img : ElfImage} {names : List String}
    (h : checkOverridesFail bytes img names = true) (addrs : List Nat) :
    resolveAddrs bytes img names ≠ .ok addrs := by
  rw [← fastResolveAddrs_eq]
  unfold checkOverridesFail at h
  split at h
  · cases h
  · rename_i e he
    rw [he]; exact fun h => nomatch h

/-! ## Constructors and fail-closed eliminators for the override judgments -/

theorem ElfRunsToWithOverrides.intro {svc : State → State} {os : List (String × (State → State))}
    {elfBytes : List (BitVec 8)} {pre : ProcessInputs → Prop}
    {post : ProcessInputs → ProcessOutcome → Prop} {oom : ProcessInputs → State → Prop}
    {img : ElfImage} {addrs : List Nat}
    (hp : ElfImage.parse elfBytes = .ok img)
    (hr : checkOverrides elfBytes img (os.map (·.1)) addrs = true)
    (h : ∀ inputs, pre inputs →
      ElfImageRunsTo img inputs (post inputs) (oom inputs) (overrideProgram svc os addrs)) :
    ElfRunsToWithOverrides svc os elfBytes pre post oom :=
  ⟨img, addrs, hp, resolveAddrs_of_check hr, h⟩

/-- Fail closed: if resolution fails, no `ElfRunsToWithOverrides` statement holds, even with an
    unsatisfiable precondition. -/
theorem ElfRunsToWithOverrides.not_of_check {svc : State → State}
    {os : List (String × (State → State))} {elfBytes : List (BitVec 8)}
    {pre : ProcessInputs → Prop} {post : ProcessInputs → ProcessOutcome → Prop}
    {oom : ProcessInputs → State → Prop}
    {img : ElfImage} (hp : ElfImage.parse elfBytes = .ok img)
    (hf : checkOverridesFail elfBytes img (os.map (·.1)) = true) :
    ¬ ElfRunsToWithOverrides svc os elfBytes pre post oom := by
  rintro ⟨img', addrs, hp', hr, -⟩
  rw [hp] at hp'
  cases hp'
  exact resolveAddrs_fail_of_check hf addrs hr

end Arm64.Process
