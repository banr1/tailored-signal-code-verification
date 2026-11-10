/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Process

/-!
# Process Input Validity and Loader Totality

Decision-procedure equivalences (`ProcessInit.check_iff_valid`, `ProcessInputs.check_iff_valid`),
canonical path and stack-fit bounds, initial file-system tree invariants, and loader totality
(`buildInitialStack_ok_of_valid`, `loadState_ok_of_valid`) for `ProcessInputs.Valid`.
-/

@[expose] public section

namespace Arm64.Process

/-! ## `Bool` Mirror Equivalence -/

theorem nodupCheck_iff_pairwise {α : Type} [DecidableEq α] (xs : List α) :
    nodupCheck xs = true ↔ xs.Pairwise (· ≠ ·) := by
  induction xs with
  | nil => simp [nodupCheck]
  | cons x xs ih =>
    simp only [nodupCheck, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not, List.pairwise_cons, ih]
    constructor
    · rintro ⟨hx, hpw⟩
      exact ⟨fun y hy hxy => hx (hxy ▸ hy), hpw⟩
    · rintro ⟨hall, hpw⟩
      exact ⟨fun hx => hall x hx rfl, hpw⟩

theorem ArgsValid.check_iff (i : ProcessInputs) :
    ArgsValid.check i = true ↔ ArgsValid i := by
  unfold ArgsValid.check
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true, List.contains_eq_mem, decide_eq_false_iff_not, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩
    exact ⟨h1, ⟨h2, h3, h4⟩, h5, h6, h7⟩
  · rintro ⟨h1, ⟨h2, h3, h4⟩, h5, h6, h7⟩
    exact ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩

theorem AuxvValid.check_iff (a : AuxvConfig) :
    AuxvValid.check a = true ↔ AuxvValid a := by
  unfold AuxvValid.check
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
    nodupCheck_iff_pairwise, List.all_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not, bne_iff_ne]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h33⟩, h8⟩, h9⟩
    refine ⟨h1, h2, ⟨h3, h4⟩, h5, ⟨h6, h7⟩, h33, h8, fun e he h51 => ?_⟩
    rcases h9 e he with hne | hb
    · exact absurd h51 hne
    · exact hb
  · rintro ⟨h1, h2, ⟨h3, h4⟩, h5, ⟨h6, h7⟩, h33, h8, h9⟩
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h33⟩, h8⟩, fun e he => ?_⟩
    by_cases h51 : e.1 = 51#64
    · exact Or.inr (h9 e he h51)
    · exact Or.inl h51

theorem StackValid.check_iff (init : ProcessInit) :
    StackValid.check init = true ↔ StackValid init := by
  unfold StackValid.check
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩
    exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5, h6, h7⟩
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5, h6, h7⟩
    exact ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩

theorem ProcessInit.check_iff_valid (init : ProcessInit) :
    init.check = true ↔ init.Valid := by
  unfold ProcessInit.check ProcessInit.Valid
  simp only [Bool.and_eq_true, AuxvValid.check_iff, StackValid.check_iff]

theorem SegValid.check_iff (seg : String) :
    SegValid.check seg = true ↔ SegValid seg := by
  unfold SegValid.check SegValid
  simp only [Bool.and_eq_true, bne_iff_ne, List.all_eq_true, decide_eq_true_eq, and_assoc]

theorem InputPathValid.check_iff (p : String) :
    InputPathValid.check p = true ↔ InputPathValid p := by
  unfold InputPathValid.check InputPathValid
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true, SegValid.check_iff, and_assoc]

private theorem isPrefixOf_iff_isPrefix {α : Type} [DecidableEq α] (l₁ l₂ : List α) :
    l₁.isPrefixOf l₂ = true ↔ l₁ <+: l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp [List.isPrefixOf]
  | cons x xs ih =>
    cases l₂ with
    | nil => simp [List.isPrefixOf]
    | cons y ys =>
      simp only [List.isPrefixOf, Bool.and_eq_true, beq_iff_eq, ih, List.cons_prefix_cons]

theorem FsValid.check_iff (i : ProcessInputs) :
    FsValid.check i = true ↔ FsValid i := by
  unfold FsValid.check
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true,
    InputPathValid.check_iff, nodupCheck_iff_pairwise, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨⟨⟨⟨⟨hd, hf⟩, hnd⟩, hsz⟩, hcl⟩, hne⟩
    refine ⟨⟨hd, hf⟩, hnd, hsz, ?_, ?_⟩
    · intro f hfm d hdm hp
      have := hcl f hfm d hdm
      rw [Bool.eq_false_iff] at this
      exact this ((isPrefixOf_iff_isPrefix _ _).mpr hp)
    · intro f hfm g hgm hp
      rcases hne f hfm g hgm with hnot | heq
      · rw [Bool.eq_false_iff] at hnot
        exact absurd ((isPrefixOf_iff_isPrefix _ _).mpr hp) hnot
      · exact heq
  · rintro ⟨⟨hd, hf⟩, hnd, hsz, hcl, hne⟩
    refine ⟨⟨⟨⟨⟨hd, hf⟩, hnd⟩, hsz⟩, ?_⟩, ?_⟩
    · intro f hfm d hdm
      rw [Bool.eq_false_iff]
      intro hp
      exact hcl f hfm d hdm ((isPrefixOf_iff_isPrefix _ _).mp hp)
    · intro f hfm g hgm
      by_cases hp : normalizePath f.1 <+: normalizePath g.1
      · exact Or.inr (hne f hfm g hgm hp)
      · left
        rw [Bool.eq_false_iff]
        intro hb
        exact hp ((isPrefixOf_iff_isPrefix _ _).mp hb)

theorem ProcessInputs.check_iff_valid (i : ProcessInputs) :
    i.check = true ↔ i.Valid := by
  unfold ProcessInputs.check ProcessInputs.Valid
  simp only [Bool.and_eq_true, ArgsValid.check_iff, ProcessInit.check_iff_valid,
    FsValid.check_iff, and_assoc]

instance (priority := high) (i : ProcessInputs) : Decidable (ArgsValid i) :=
  decidable_of_iff (ArgsValid.check i = true) (ArgsValid.check_iff i)

instance (priority := high) (a : AuxvConfig) : Decidable (AuxvValid a) :=
  decidable_of_iff (AuxvValid.check a = true) (AuxvValid.check_iff a)

instance (priority := high) (init : ProcessInit) : Decidable (StackValid init) :=
  decidable_of_iff (StackValid.check init = true) (StackValid.check_iff init)

instance (priority := high) (init : ProcessInit) : Decidable init.Valid :=
  decidable_of_iff (init.check = true) (ProcessInit.check_iff_valid init)

instance (priority := high) : DecidablePred ProcessInit.Valid :=
  fun init => decidable_of_iff (init.check = true) (ProcessInit.check_iff_valid init)

instance (priority := high) (seg : String) : Decidable (SegValid seg) :=
  decidable_of_iff (SegValid.check seg = true) (SegValid.check_iff seg)

instance (priority := high) (p : String) : Decidable (InputPathValid p) :=
  decidable_of_iff (InputPathValid.check p = true) (InputPathValid.check_iff p)

instance (priority := high) (i : ProcessInputs) : Decidable (FsValid i) :=
  decidable_of_iff (FsValid.check i = true) (FsValid.check_iff i)

instance (priority := high) (i : ProcessInputs) : Decidable i.Valid :=
  decidable_of_iff (i.check = true) (ProcessInputs.check_iff_valid i)

instance (priority := high) : DecidablePred ProcessInputs.Valid :=
  fun i => decidable_of_iff (i.check = true) (ProcessInputs.check_iff_valid i)

/-! ## Canonical Path and Stack-Fit Bounds -/

theorem InputPathValid.not_hasDotDot {p : String} (hp : InputPathValid p) :
    hasDotDot p = false := by
  unfold hasDotDot
  rw [Bool.eq_false_iff]
  intro hc
  rw [List.contains_eq_mem, decide_eq_true_eq] at hc
  exact (hp.2.2 ".." hc).2.2.1 rfl

theorem InputPathValid.normalizePath_eq_splitSlash {p : String} (hp : InputPathValid p) :
    normalizePath p = splitSlash p := by
  unfold normalizePath
  rw [List.filter_eq_self]
  intro seg hseg
  have hs := hp.2.2 seg hseg
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne]
  refine ⟨?_, hs.2.1⟩
  rw [Bool.eq_false_iff]
  intro h
  exact hs.1 (String.isEmpty_iff.mp h)

theorem InputPathValid.normalizePath_ne_nil {p : String} (hp : InputPathValid p) :
    normalizePath p ≠ [] := by
  rw [hp.normalizePath_eq_splitSlash]
  exact hp.2.1

theorem StackValid.stackSize_ge {init : ProcessInit} (hs : StackValid init) :
    STK_LIM ≤ init.stackSize :=
  hs.size_floor

theorem StackValid.stackSize_le {init : ProcessInit} (hs : StackValid init) :
    init.stackSize ≤ STACK_SIZE_MAX :=
  hs.size_ceil

theorem StackValid.argLimit_le_quarter {init : ProcessInit} (hs : StackValid init) :
    argLimit init.stackSize ≤ init.stackSize / 4 := by
  unfold argLimit ARG_MAX STK_LIM
  have hfl := hs.size_floor
  unfold STK_LIM at hfl
  omega

theorem ProcessInit.Valid.auxv {init : ProcessInit} (h : init.Valid) :
    AuxvValid init.auxv := h.1

theorem ProcessInit.Valid.stack {init : ProcessInit} (h : init.Valid) :
    StackValid init := h.2

theorem ProcessInit.Valid.stackSize_ge {init : ProcessInit} (h : init.Valid) :
    STK_LIM ≤ init.stackSize :=
  h.2.size_floor

theorem ProcessInit.Valid.stackSize_le {init : ProcessInit} (h : init.Valid) :
    init.stackSize ≤ STACK_SIZE_MAX :=
  h.2.size_ceil

theorem ProcessInputs.Valid.args {i : ProcessInputs} (hv : i.Valid) :
    ArgsValid i := hv.1

theorem ProcessInputs.Valid.init {i : ProcessInputs} (hv : i.Valid) :
    i.init.Valid := hv.2.1

theorem ProcessInputs.Valid.auxv {i : ProcessInputs} (hv : i.Valid) :
    AuxvValid i.init.auxv := hv.2.1.1

theorem ProcessInputs.Valid.stack {i : ProcessInputs} (hv : i.Valid) :
    StackValid i.init := hv.2.1.2

theorem ProcessInputs.Valid.fs {i : ProcessInputs} (hv : i.Valid) :
    FsValid i := hv.2.2

theorem ProcessInputs.Valid.stackSize_ge {i : ProcessInputs} (hv : i.Valid) :
    STK_LIM ≤ i.init.stackSize :=
  hv.2.1.stackSize_ge

theorem ProcessInputs.Valid.stackSize_le {i : ProcessInputs} (hv : i.Valid) :
    i.init.stackSize ≤ STACK_SIZE_MAX :=
  hv.2.1.stackSize_le

theorem AuxvValid.minsigstksz_of_mem {a : AuxvConfig} (ha : AuxvValid a) {v : BitVec 64}
    (hm : (51#64, v) ∈ a.extra) : v.toNat ≤ 524288 :=
  ha.minsigstksz_bound (51#64, v) hm rfl

theorem ProcessInputs.Valid.minsigstksz_of_mem {i : ProcessInputs} (hv : i.Valid) {v : BitVec 64}
    (hm : (51#64, v) ∈ i.init.auxv.extra) : v.toNat ≤ 524288 :=
  hv.auxv.minsigstksz_of_mem hm

theorem ArgsValid.argc_envc_le {i : ProcessInputs} (ha : ArgsValid i) :
    8 * (i.argv.length + i.envp.length) + 1 ≤ argLimit i.init.stackSize := by
  have ht := ha.total
  unfold argBytes at ht
  omega

private theorem foldl_len_add (init : Nat) (xs : List (List (BitVec 8))) :
    xs.foldl (fun n s => n + s.length + 1) init =
      init + xs.foldl (fun n s => n + (s.length + 1)) 0 := by
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [ih (init + x.length + 1)]
    have hfold : ∀ (k : Nat) (l : List (List (BitVec 8))),
        l.foldl (fun n s => n + (s.length + 1)) k =
          k + l.foldl (fun n s => n + (s.length + 1)) 0 := by
      intro k l
      induction l generalizing k with
      | nil => simp
      | cons y ys ihy =>
        simp only [List.foldl_cons, Nat.zero_add]
        rw [ihy (k + (y.length + 1)), ihy (y.length + 1)]
        omega
    rw [hfold (x.length + 1) xs]
    omega

private theorem packCStringList_len (base : BitVec 64) (xs : List (List (BitVec 8))) :
    (packCStringList base xs).1 = xs.foldl (fun n s => n + (s.length + 1)) 0 ∧
    (packCStringList base xs).2.1.length = xs.foldl (fun n s => n + (s.length + 1)) 0 ∧
    (packCStringList base xs).2.2.length = xs.length := by
  have hfold_add : ∀ (k : Nat) (l : List (List (BitVec 8))),
      l.foldl (fun n s => n + (s.length + 1)) k =
        k + l.foldl (fun n s => n + (s.length + 1)) 0 := by
    intro k l
    induction l generalizing k with
    | nil => simp
    | cons y ys ihy =>
      simp only [List.foldl_cons, Nat.zero_add]
      rw [ihy (k + (y.length + 1)), ihy (y.length + 1)]
      omega
  have hgen : ∀ (l : List (List (BitVec 8))) (off : Nat)
      (accB : List (BitVec 8)) (accA : List (BitVec 64)),
      let res := l.foldl
        (fun (o, b, a) s =>
          let entry := s ++ [0#8]
          let addr := base + BitVec.ofNat 64 o
          (o + entry.length, b ++ entry, a ++ [addr]))
        (off, accB, accA)
      res.1 = off + l.foldl (fun n s => n + (s.length + 1)) 0 ∧
      res.2.1.length = accB.length + l.foldl (fun n s => n + (s.length + 1)) 0 ∧
      res.2.2.length = accA.length + l.length := by
    intro l
    induction l with
    | nil =>
      intro off accB accA
      simp
    | cons s rest ih =>
      intro off accB accA
      simp only [List.foldl_cons, Nat.zero_add]
      obtain ⟨h1, h2, h3⟩ := ih (off + (s ++ [0#8]).length) (accB ++ (s ++ [0#8]))
        (accA ++ [base + BitVec.ofNat 64 off])
      dsimp only at h1 h2 h3 ⊢
      rw [h1, h2, h3]
      simp only [List.length_append, List.length_cons, List.length_nil]
      rw [hfold_add (s.length + 1) rest]
      exact ⟨by omega, by omega, by omega⟩
  simpa [packCStringList] using hgen xs 0 [] []

private theorem flatMap_bytesLE8_len (ws : List (BitVec 64)) :
    (ws.flatMap (Obj.bytesLE 8)).length = 8 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, ih]
    have h8 : (Obj.bytesLE 8 w).length = 8 := by simp [Obj.bytesLE]
    omega

private theorem flatMap_pair_len (ps : List (BitVec 64 × BitVec 64)) :
    (ps.flatMap fun (t, v) => [t, v]).length = 2 * ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨t, v⟩
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]
    omega

/-- Under `inputs.Valid` and `img.brkStart ≤ stackBase`, `buildInitialStack` succeeds with a
    16-byte-aligned `sp` and leaves more than half of `inputs.init.stackSize` free below `sp`. -/
theorem buildInitialStack_ok_of_valid (img : ElfImage) {i : ProcessInputs}
    (hv : i.Valid) (hbrk : img.brkStart.toNat ≤ i.init.stackTop.toNat - i.init.stackSize) :
    ∃ sp stackRegion,
      buildInitialStack img i = .ok (sp, stackRegion) ∧
      sp.toNat % 16 = 0 ∧
      i.init.stackTop.toNat - i.init.stackSize + i.init.stackSize / 2 ≤ sp.toNat ∧
      sp.toNat + stackRegion.bytes.length = i.init.stackTop.toNat ∧
      stackRegion.start = sp ∧
      stackRegion.perm = Perm.rw := by
  rcases hv with ⟨ha, ⟨hx, hs⟩, _⟩
  have hr16 : (i.init.auxv.randomBytes.length != 16) = false := by
    rw [bne_eq_false_iff_eq]; exact hx.random16
  have hanul : (i.argv.any (fun s => s.contains 0#8)) = false := by
    rw [Bool.eq_false_iff]; intro h; rw [List.any_eq_true] at h
    rcases h with ⟨s, hsm, hc⟩
    exact ha.no_nul.1 s hsm (List.contains_iff_mem.mp hc)
  have henul : (i.envp.any (fun s => s.contains 0#8)) = false := by
    rw [Bool.eq_false_iff]; intro h; rw [List.any_eq_true] at h
    rcases h with ⟨s, hsm, hc⟩
    exact ha.no_nul.2.1 s hsm (List.contains_iff_mem.mp hc)
  have hxnul : i.execfn.contains 0#8 = false := by
    rw [Bool.eq_false_iff]; intro hc
    exact ha.no_nul.2.2 (List.contains_iff_mem.mp hc)
  have hpage : Obj.pageSize = 4096 := rfl
  have hfloor : 524288 ≤ i.init.stackSize := by
    have := hs.size_floor; unfold STK_LIM at this; omega
  have halign_chk :
      (i.init.stackTop.toNat % Obj.pageSize != 0 || i.init.stackSize == 0 || i.init.stackSize % Obj.pageSize != 0) = false := by
    simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq, beq_eq_false_iff_ne]
    exact ⟨⟨hs.top_aligned.1, by omega⟩, hs.size_aligned.1⟩
  have hunder : ¬ (i.init.stackSize > i.init.stackTop.toNat) := by
    have := hs.size_aligned.2; omega
  have hoverlap : ¬ (img.brkStart.toNat > i.init.stackTop.toNat - i.init.stackSize) := by omega
  have harg_lim := hs.argLimit_le_quarter
  have harg_tot := ha.total
  have hf_argv := foldl_len_add 0 i.argv
  have hf_envp := foldl_len_add 0 i.envp
  simp only [Nat.zero_add] at hf_argv hf_envp
  let platformBytes : List (BitVec 8) :=
    [0x61#8, 0x61#8, 0x72#8, 0x63#8, 0x68#8, 0x36#8, 0x34#8, 0x00#8]
  let execfnBytes : List (BitVec 8) := i.execfn ++ [0#8]
  let topSentinelBytes : List (BitVec 8) := List.replicate 8 0#8
  let upperRaw :=
    platformBytes.length +
    i.argv.foldl (fun n s => n + s.length + 1) 0 +
    i.envp.foldl (fun n s => n + s.length + 1) 0 +
    execfnBytes.length + topSentinelBytes.length
  have hplat_len : platformBytes.length = 8 := rfl
  have hsent_len : topSentinelBytes.length = 8 := rfl
  have hexec_len : execfnBytes.length = i.execfn.length + 1 := by simp [execfnBytes]
  have hraw_eq : upperRaw + 8 * (i.argv.length + i.envp.length) = 16 + argBytes i := by
    dsimp only [upperRaw]
    unfold argBytes
    rw [hplat_len, hsent_len, hexec_len, hf_argv, hf_envp]
    omega
  have halign16_le : alignUp16 upperRaw ≤ upperRaw + 15 := by unfold alignUp16; omega
  have halign16_ge : upperRaw ≤ alignUp16 upperRaw := by unfold alignUp16; omega
  have halign16_mod : alignUp16 upperRaw % 16 = 0 := by unfold alignUp16; omega
  have hinfo_gt : ¬ (16 + alignUp16 upperRaw > i.init.stackSize) := by omega
  let infoPadLen := alignUp16 upperRaw - upperRaw
  let infoLen := 16 + alignUp16 upperRaw
  let infoBaseNat := i.init.stackTop.toNat - infoLen
  let infoBase := BitVec.ofNat 64 infoBaseNat
  let platformAddr := infoBase + BitVec.ofNat 64 (16 + infoPadLen)
  let argvBase := platformAddr + BitVec.ofNat 64 platformBytes.length
  have ⟨hp1_off, hp1_b, hp1_a⟩ := packCStringList_len argvBase i.argv
  rcases hp1 : packCStringList argvBase i.argv with ⟨off1, argvBytes, argvAddrs⟩
  simp only [hp1] at hp1_off hp1_b hp1_a
  let envpBase := argvBase + BitVec.ofNat 64 off1
  have ⟨hp2_off, hp2_b, hp2_a⟩ := packCStringList_len envpBase i.envp
  rcases hp2 : packCStringList envpBase i.envp with ⟨off2, envpBytes, envpAddrs⟩
  simp only [hp2] at hp2_off hp2_b hp2_a
  let execfnAddr := envpBase + BitVec.ofNat 64 off2
  let infoBytes :=
    i.init.auxv.randomBytes ++ List.replicate infoPadLen 0#8 ++
    platformBytes ++ argvBytes ++ envpBytes ++ execfnBytes ++ topSentinelBytes
  have hinfo_bytes_len : infoBytes.length = infoLen := by
    dsimp only [infoBytes, infoLen, infoPadLen]
    simp only [List.length_append, List.length_replicate, hx.random16, hplat_len, hsent_len,
      hexec_len, hp1_b, hp2_b]
    have hraw_def : upperRaw =
        8 + i.argv.foldl (fun n s => n + (s.length + 1)) 0 +
        i.envp.foldl (fun n s => n + (s.length + 1)) 0 +
        (i.execfn.length + 1) + 8 := by
      dsimp only [upperRaw]; rw [hplat_len, hsent_len, hexec_len, hf_argv, hf_envp]
    omega
  let auxvPairs : List (BitVec 64 × BitVec 64) :=
    [ (AuxvTag.phdr, img.phdrVaddr), (AuxvTag.phent, BitVec.ofNat 64 img.phent)
    , (AuxvTag.phnum, BitVec.ofNat 64 img.phnum), (AuxvTag.pagesz, BitVec.ofNat 64 Obj.pageSize)
    , (AuxvTag.base, 0#64), (AuxvTag.flags, 0#64), (AuxvTag.entry, img.entry)
    , (AuxvTag.uid, i.init.auxv.uid), (AuxvTag.euid, i.init.auxv.euid)
    , (AuxvTag.gid, i.init.auxv.gid), (AuxvTag.egid, i.init.auxv.egid)
    , (AuxvTag.platform, platformAddr), (AuxvTag.hwcap, i.init.auxv.hwcap)
    , (AuxvTag.clktck, 100#64), (AuxvTag.secure, i.init.auxv.secure)
    , (AuxvTag.random, infoBase), (AuxvTag.hwcap2, i.init.auxv.hwcap2)
    , (AuxvTag.execfn, execfnAddr) ] ++
    i.init.auxv.extra ++ [ (AuxvTag.null, 0#64) ]
  have hauxv_len : auxvPairs.length = 19 + i.init.auxv.extra.length := by
    dsimp only [auxvPairs]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  let unpaddedWords :=
    ([BitVec.ofNat 64 i.argv.length] ++ argvAddrs ++ [0#64] ++ envpAddrs ++ [0#64]) ++
    (auxvPairs.flatMap fun (t, v) => [t, v])
  have hunpad_len : unpaddedWords.length = 3 + i.argv.length + i.envp.length + 2 * auxvPairs.length := by
    dsimp only [unpaddedWords]
    simp only [List.length_append, List.length_cons, List.length_nil, hp1_a, hp2_a, flatMap_pair_len]
    omega
  let tableWords := if unpaddedWords.length % 2 == 0 then unpaddedWords else unpaddedWords ++ [0#64]
  have htw_even : tableWords.length % 2 = 0 ∧ tableWords.length ≤ unpaddedWords.length + 1 := by
    dsimp only [tableWords]
    split
    · rename_i hev; rw [beq_iff_eq] at hev; exact ⟨hev, by omega⟩
    · rename_i hodd; rw [Bool.not_eq_true, beq_eq_false_iff_ne] at hodd
      simp only [List.length_append, List.length_singleton]; omega
  let tableBytes := tableWords.flatMap (Obj.bytesLE 8)
  have htb_len : tableBytes.length = 8 * tableWords.length := flatMap_bytesLE8_len tableWords
  have htot_fit : tableBytes.length + infoBytes.length ≤ i.init.stackSize / 4 + 480 := by
    have := hx.extra_le
    omega
  have htot_gt : ¬ (tableBytes.length + infoBytes.length > i.init.stackSize) := by omega
  let spNat := infoBaseNat - tableBytes.length
  let sp := BitVec.ofNat 64 spNat
  let stackRegion : Snapshot.Region :=
    { start := sp, perm := Perm.rw, bytes := tableBytes ++ infoBytes }
  have hbuild : buildInitialStack img i = .ok (sp, stackRegion) := by
    unfold buildInitialStack
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure,
      hr16, hanul, henul, hxnul, halign_chk, hunder, hoverlap, Bool.false_eq_true, ↓reduceIte]
    rw [ite_eq_right_iff.mpr fun h => (hinfo_gt h).elim]
    change (match packCStringList argvBase i.argv with
      | (off1, argvBytes, argvAddrs) => _) = _
    rw [hp1]
    dsimp only
    change (match packCStringList envpBase i.envp with
      | (off2, envpBytes, envpAddrs) => _) = _
    rw [hp2]
    dsimp only
    rw [ite_eq_right_iff.mpr fun h => (htot_gt h).elim]
  have htop_lt : i.init.stackTop.toNat < 2 ^ 64 := i.init.stackTop.isLt
  have htop_mod16 : i.init.stackTop.toNat % 16 = 0 := by
    have := hs.top_aligned.1; rw [hpage] at this; omega
  have hsp_toNat : sp.toNat = spNat := by
    dsimp only [sp]
    have := hs.size_aligned.2
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by dsimp only [spNat, infoBaseNat, infoLen]; omega)]
  refine ⟨sp, stackRegion, hbuild, ?_, ?_, ?_, rfl, rfl⟩
  · rw [hsp_toNat]; dsimp only [spNat, infoBaseNat, infoLen]; have := hs.size_aligned.2; omega
  · rw [hsp_toNat]; dsimp only [spNat, infoBaseNat, infoLen]; have := hs.size_aligned.2; omega
  · rw [hsp_toNat]; dsimp only [stackRegion, spNat, infoBaseNat]
    rw [List.length_append, hinfo_bytes_len]; have := hs.size_aligned.2; omega

/-- Under `inputs.Valid`, `img.WellFormed`, and `img.brkStart ≤ stackBase`, `ElfImage.loadState`
    succeeds. -/
theorem loadState_ok_of_valid (img : ElfImage) {i : ProcessInputs}
    (hv : i.Valid) (hwf : img.WellFormed = true)
    (hbrk : img.brkStart.toNat ≤ i.init.stackTop.toNat - i.init.stackSize) :
    ∃ s0, img.loadState i = .ok s0 := by
  obtain ⟨sp, sr, hbuild, _⟩ := buildInitialStack_ok_of_valid img hv hbrk
  rcases hv with ⟨_, _, hfs⟩
  unfold ElfImage.loadState
  have hwf' : (!img.WellFormed) = false := by rw [hwf]; rfl
  have hdirs : (i.dirs.any (fun d => hasLeadingSlash d || hasDotDot d)) = false := by
    rw [Bool.eq_false_iff]; intro h; rw [List.any_eq_true] at h
    rcases h with ⟨d, hdm, hbad⟩
    have hd := hfs.paths.1 d hdm
    rw [hd.1, hd.not_hasDotDot] at hbad; cases hbad
  have hfiles : (i.files.any (fun (p, bs) =>
      hasLeadingSlash p || hasDotDot p || !decide (bs.length ≤ MAX_LFS_FILESIZE))) = false := by
    rw [Bool.eq_false_iff]; intro h; rw [List.any_eq_true] at h
    rcases h with ⟨⟨p, bs⟩, hfm, hbad⟩
    dsimp only at hbad
    have hf := hfs.paths.2 (p, bs) hfm
    have hsz : decide (bs.length ≤ MAX_LFS_FILESIZE) = true := decide_eq_true (hfs.file_size (p, bs) hfm)
    rw [hf.1, hf.not_hasDotDot, hsz] at hbad; cases hbad
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure,
    hwf', hdirs, hfiles, hbuild, Bool.false_eq_true, ↓reduceIte]
  exact ⟨_, rfl⟩

theorem loadState_ok_of_valid_low_brk (img : ElfImage) {i : ProcessInputs}
    (hv : i.Valid) (hwf : img.WellFormed = true)
    (hbrk : img.brkStart.toNat ≤ STACK_BASE_MIN) :
    ∃ s0, img.loadState i = .ok s0 :=
  loadState_ok_of_valid img hv hwf (Nat.le_trans hbrk hv.stack.base_floor)

/-! ## Initial File-System Tree Invariants -/

private theorem dropLast_map {α β : Type} (f : α → β) :
    ∀ (l : List α), (l.map f).dropLast = l.dropLast.map f
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by
    change f a :: (List.map f (b :: rest)).dropLast = f a :: (b :: rest).dropLast.map f
    rw [dropLast_map f (b :: rest)]

private theorem mem_nonEmptyPrefixes {q ks : FsPath} :
    q ∈ FsPath.nonEmptyPrefixes ks ↔ q ≠ [] ∧ q <+: ks := by
  induction ks generalizing q with
  | nil => simp [FsPath.nonEmptyPrefixes]
  | cons k rest ih =>
    simp only [FsPath.nonEmptyPrefixes, List.mem_cons, List.mem_map]
    constructor
    · rintro (rfl | ⟨r, hr, rfl⟩)
      · exact ⟨by simp, ⟨rest, rfl⟩⟩
      · obtain ⟨_, hp⟩ := ih.mp hr
        exact ⟨by simp, List.cons_prefix_cons.mpr ⟨rfl, hp⟩⟩
    · rintro ⟨hq, hp⟩
      cases q with
      | nil => exact (hq rfl).elim
      | cons q0 qs =>
        obtain ⟨rfl, hp'⟩ := List.cons_prefix_cons.mp hp
        cases qs with
        | nil => exact Or.inl rfl
        | cons q1 qr => exact Or.inr ⟨q1 :: qr, ih.mpr ⟨by simp, hp'⟩, rfl⟩

private theorem mem_dropLast_nonEmptyPrefixes {q ks : FsPath} :
    q ∈ (FsPath.nonEmptyPrefixes ks).dropLast ↔ q ≠ [] ∧ q <+: ks ∧ q ≠ ks := by
  induction ks generalizing q with
  | nil => simp [FsPath.nonEmptyPrefixes]
  | cons k rest ih =>
    cases rest with
    | nil =>
      simp only [FsPath.nonEmptyPrefixes, List.map_nil, List.dropLast_singleton,
        List.not_mem_nil, false_iff, not_and]
      intro hq hp hne
      cases q with
      | nil => exact hq rfl
      | cons a as =>
        obtain ⟨rfl, hp'⟩ := List.cons_prefix_cons.mp hp
        rw [List.prefix_nil] at hp'; subst hp'
        exact hne rfl
    | cons k2 rest2 =>
      have hne_map : ((FsPath.nonEmptyPrefixes (k2 :: rest2)).map (k :: ·)) ≠ [] := by
        simp [FsPath.nonEmptyPrefixes]
      rw [FsPath.nonEmptyPrefixes, List.dropLast_cons_of_ne_nil hne_map, dropLast_map]
      simp only [List.mem_cons, List.mem_map]
      constructor
      · rintro (rfl | ⟨r, hr, rfl⟩)
        · exact ⟨by simp, ⟨k2 :: rest2, rfl⟩, by simp⟩
        · obtain ⟨_, hp, hne⟩ := ih.mp hr
          exact ⟨by simp, List.cons_prefix_cons.mpr ⟨rfl, hp⟩, fun hc => hne (List.cons.inj hc).2⟩
      · rintro ⟨hq, hp, hne⟩
        cases q with
        | nil => exact (hq rfl).elim
        | cons q0 qs =>
          obtain ⟨rfl, hp'⟩ := List.cons_prefix_cons.mp hp
          cases qs with
          | nil => exact Or.inl rfl
          | cons q1 qr =>
            exact Or.inr ⟨q1 :: qr, ih.mpr ⟨by simp, hp', fun hc => hne (by rw [hc])⟩, rfl⟩

private theorem prefix_antisymm {α : Type} :
    ∀ {a b : List α}, a <+: b → b <+: a → a = b
  | [], [], _, _ => rfl
  | [], _ :: _, _, h2 => by rw [List.prefix_nil] at h2; cases h2
  | _ :: _, [], h1, _ => by rw [List.prefix_nil] at h1; cases h1
  | x :: xs, y :: ys, h1, h2 => by
    obtain ⟨rfl, h1'⟩ := List.cons_prefix_cons.mp h1
    obtain ⟨_, h2'⟩ := List.cons_prefix_cons.mp h2
    rw [prefix_antisymm h1' h2']

private theorem setEntry_entries_eq (fs : FsState) (p k : FsPath) (e : Option FsEntry) :
    (fs.setEntry p e).entries k = if k = p then e else fs.entries k := by
  unfold FsState.setEntry
  dsimp only
  by_cases h : k = p
  · subst h; simp
  · have hb : (k == p) = false := beq_eq_false_iff_ne.mpr h
    simp [h, hb]

private theorem foldl_setDir_entries (prefs : List FsPath) (fs : FsState) (k : FsPath) :
    (prefs.foldl (fun acc pref => acc.setEntry pref (some .dir)) fs).entries k =
      if k ∈ prefs then some .dir else fs.entries k := by
  induction prefs generalizing fs with
  | nil => simp
  | cons p ps ih =>
    rw [List.foldl_cons, ih, setEntry_entries_eq]
    by_cases hkp : k = p
    · subst hkp; simp
    · simp [hkp]

private theorem foldl_dirs_entries (dirs : List String) (fs : FsState) (k : FsPath) :
    (dirs.foldl (fun acc d => (FsPath.nonEmptyPrefixes (normalizePath d)).foldl
      (fun a pref => a.setEntry pref (some .dir)) acc) fs).entries k =
      if ∃ d ∈ dirs, k ∈ FsPath.nonEmptyPrefixes (normalizePath d) then some .dir
      else fs.entries k := by
  induction dirs generalizing fs with
  | nil => simp
  | cons d ds ih =>
    rw [List.foldl_cons, ih, foldl_setDir_entries]
    by_cases hrest : ∃ d' ∈ ds, k ∈ FsPath.nonEmptyPrefixes (normalizePath d')
    · rcases hrest with ⟨d', hd', hk⟩
      have hex : ∃ d'' ∈ d :: ds, k ∈ FsPath.nonEmptyPrefixes (normalizePath d'') :=
        ⟨d', List.mem_cons_of_mem _ hd', hk⟩
      rw [ite_eq_left_iff.mpr fun h => (h ⟨d', hd', hk⟩).elim,
        ite_eq_left_iff.mpr fun h => (h hex).elim]
    · rw [ite_eq_right_iff.mpr fun h => (hrest h).elim]
      by_cases hd : k ∈ FsPath.nonEmptyPrefixes (normalizePath d)
      · have hex : ∃ d'' ∈ d :: ds, k ∈ FsPath.nonEmptyPrefixes (normalizePath d'') :=
          ⟨d, List.mem_cons_self .., hd⟩
        rw [ite_eq_left_iff.mpr fun h => (h hd).elim,
          ite_eq_left_iff.mpr fun h => (h hex).elim]
      · have hnot : ¬ ∃ d'' ∈ d :: ds, k ∈ FsPath.nonEmptyPrefixes (normalizePath d'') := by
          rintro ⟨d'', hm, hk⟩
          rcases List.mem_cons.mp hm with rfl | hds
          · exact hd hk
          · exact hrest ⟨d'', hds, hk⟩
        rw [ite_eq_right_iff.mpr fun h => (hd h).elim,
          ite_eq_right_iff.mpr fun h => (hnot h).elim]

private theorem foldl_files_entries (files : List (String × List (BitVec 8))) (fs : FsState)
    (hnodup : (files.map (fun f => normalizePath f.1)).Pairwise (· ≠ ·))
    (hnonest : ∀ f ∈ files, ∀ g ∈ files,
      normalizePath f.1 <+: normalizePath g.1 → normalizePath f.1 = normalizePath g.1) :
    ∀ k : FsPath,
      ((∀ f ∈ files, normalizePath f.1 ≠ k) →
        (files.foldl (fun acc (p, bs) =>
          let withAnc := ((FsPath.nonEmptyPrefixes (normalizePath p)).dropLast).foldl
            (fun a pref => a.setEntry pref (some .dir)) acc
          withAnc.setFile p (some (.file bs))) fs).entries k =
          if ∃ f ∈ files, k ∈ (FsPath.nonEmptyPrefixes (normalizePath f.1)).dropLast then some .dir
          else fs.entries k) ∧
      (∀ p bs, (p, bs) ∈ files → k = normalizePath p →
        (files.foldl (fun acc (p', bs') =>
          let withAnc := ((FsPath.nonEmptyPrefixes (normalizePath p')).dropLast).foldl
            (fun a pref => a.setEntry pref (some .dir)) acc
          withAnc.setFile p' (some (.file bs'))) fs).entries k = some (.file bs)) := by
  induction files generalizing fs with
  | nil =>
    intro k
    exact ⟨by simp, by intro _ _ hm; cases hm⟩
  | cons f rest ih =>
    rcases f with ⟨p0, bs0⟩
    rw [List.map_cons, List.pairwise_cons] at hnodup
    rcases hnodup with ⟨hnot_in_rest, hnodup_rest⟩
    have hnonest_rest : ∀ f ∈ rest, ∀ g ∈ rest,
        normalizePath f.1 <+: normalizePath g.1 → normalizePath f.1 = normalizePath g.1 :=
      fun f hf g hg => hnonest f (List.mem_cons_of_mem _ hf) g (List.mem_cons_of_mem _ hg)
    let stepFs :=
      (((FsPath.nonEmptyPrefixes (normalizePath p0)).dropLast).foldl
        (fun a pref => a.setEntry pref (some .dir)) fs).setFile p0 (some (.file bs0))
    intro k
    obtain ⟨ih_nonfile, ih_file⟩ := ih stepFs hnodup_rest hnonest_rest k
    constructor
    · intro hne_all
      have hne0 : normalizePath p0 ≠ k := hne_all (p0, bs0) (List.mem_cons_self ..)
      have hne_rest : ∀ f ∈ rest, normalizePath f.1 ≠ k :=
        fun f hf => hne_all f (List.mem_cons_of_mem _ hf)
      simp only [List.foldl_cons]
      rw [ih_nonfile hne_rest]
      have hstep : stepFs.entries k =
          if k ∈ (FsPath.nonEmptyPrefixes (normalizePath p0)).dropLast then some .dir
          else fs.entries k := by
        dsimp only [stepFs, FsState.setFile]
        rw [setEntry_entries_eq, ite_eq_right_iff.mpr fun h => (hne0 (Eq.symm h)).elim,
          foldl_setDir_entries]
      rw [hstep]
      by_cases hrest : ∃ f ∈ rest, k ∈ (FsPath.nonEmptyPrefixes (normalizePath f.1)).dropLast
      · rcases hrest with ⟨g, hg, hk⟩
        have hex : ∃ f ∈ (p0, bs0) :: rest, k ∈ (FsPath.nonEmptyPrefixes (normalizePath f.1)).dropLast :=
          ⟨g, List.mem_cons_of_mem _ hg, hk⟩
        rw [ite_eq_left_iff.mpr fun h => (h ⟨g, hg, hk⟩).elim,
          ite_eq_left_iff.mpr fun h => (h hex).elim]
      · rw [ite_eq_right_iff.mpr fun h => (hrest h).elim]
        by_cases hk0 : k ∈ (FsPath.nonEmptyPrefixes (normalizePath p0)).dropLast
        · have hex : ∃ f ∈ (p0, bs0) :: rest, k ∈ (FsPath.nonEmptyPrefixes (normalizePath f.1)).dropLast :=
            ⟨(p0, bs0), List.mem_cons_self .., hk0⟩
          rw [ite_eq_left_iff.mpr fun h => (h hk0).elim,
            ite_eq_left_iff.mpr fun h => (h hex).elim]
        · have hnot_ex : ¬ ∃ f ∈ (p0, bs0) :: rest,
              k ∈ (FsPath.nonEmptyPrefixes (normalizePath f.1)).dropLast := by
            rintro ⟨g, hg, hk⟩
            rcases List.mem_cons.mp hg with rfl | hgr
            · exact hk0 hk
            · exact hrest ⟨g, hgr, hk⟩
          rw [ite_eq_right_iff.mpr fun h => (hk0 h).elim,
            ite_eq_right_iff.mpr fun h => (hnot_ex h).elim]
    · intro p bs hm hk_eq
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hm with h_head | h_tail
      · injection h_head with hp0 hbs0
        subst hp0 hbs0 hk_eq
        have hne_rest : ∀ g ∈ rest, normalizePath g.1 ≠ normalizePath p := by
          intro g hg heq
          exact hnot_in_rest (normalizePath g.1) (List.mem_map_of_mem hg) (Eq.symm heq)
        rw [ih_nonfile hne_rest]
        have hnot_anc : ¬ ∃ g ∈ rest,
            normalizePath p ∈ (FsPath.nonEmptyPrefixes (normalizePath g.1)).dropLast := by
          rintro ⟨g, hg, hk⟩
          obtain ⟨_, hpref, hneq⟩ := mem_dropLast_nonEmptyPrefixes.mp hk
          exact hneq (hnonest (p, bs) (List.mem_cons_self ..) g (List.mem_cons_of_mem _ hg) hpref)
        rw [ite_eq_right_iff.mpr fun h => (hnot_anc h).elim]
        dsimp only [stepFs, FsState.setFile]
        rw [setEntry_entries_eq, ite_eq_left_iff.mpr fun h => (h rfl).elim]
      · exact ih_file p bs h_tail hk_eq

end Arm64.Process
