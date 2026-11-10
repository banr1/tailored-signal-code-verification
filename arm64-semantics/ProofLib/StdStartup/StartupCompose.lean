/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.StdStartup.TopInit

/-!
# Static musl and Rust `std` Startup Composition

Composes `_start` to `userMain` across musl stage 1, `static_init_tls`, `libc_start_init`,
`detect_and_initialize`, and `c_main` setup for static AArch64 `ET_EXEC` binaries matching
`StdBinaryLayout`, establishing `StdUserMainState` and splitting memory into `StdUserMainPre` and
`StdPostMainCleanup`.
-/

set_option autoImplicit false

@[expose] public section

namespace ProofLib.StdStartup

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection StdBinaryLayout

private theorem hasInstrs_withSvc {P : Program} {svc : State → State} {base : BitVec 64} {is : List Instr}
    (h : hasInstrs P base is) : hasInstrs (P.withSvc svc) base is := by
  intro i hi; rw [Program.withSvc_fetch]; exact h i hi

theorem unpack_extra_chunks {P : Program} {L : StdBinaryLayout}
    (h : CodeChunks P (stdStartupExtraChunks L)) :
    hasInstrs P L.startAddr (startInstrs L) ∧
    hasInstrs P L.startCAddr (startCInstrs L) ∧
    hasInstrs P L.libcStartMainAddr (libcStartMainInstrs L) ∧
    hasInstrs P L.initLibcAddr (initLibcInstrs L) ∧
    P.hasWords L.dummy1Addr dummy1Words ∧
    hasInstrs P L.staticInitTlsAddr (staticInitTlsInstrs L) ∧
    hasInstrs P L.copyTlsAddr (copyTlsInstrs L) ∧
    hasInstrs P L.initTpAddr (initTpInstrs L) ∧
    P.hasWords L.setThreadAreaAddr setThreadAreaWords ∧
    hasInstrs P L.libcStartMainStage2Addr (libcStartMainStage2EntryInstrs L) ∧
    hasInstrs P L.libcStartInitAddr (libcStartInitInstrs L) ∧
    P.hasWords L.initFnAddr initFnWords ∧
    hasInstrs P L.doInitAddr (doInitInstrs L) ∧
    hasInstrs P L.getauxvalAddr (getauxvalInstrs L) ∧
    hasInstrs P L.detectAndInitializeAddr (detectInitFastInstrs L) ∧
    hasInstrs P L.initLseAddr (initLseInstrs L) ∧
    hasInstrs P L.rustEnableLseAddr (rustEnableLseInstrs L) ∧
    hasInstrs P L.cas8RelaxAddr (cas8RelaxInstrs L) ∧
    hasInstrs P L.cas4AcqAddr (cas4AcqInstrs L) ∧
    hasInstrs P L.cas8AcqAddr (cas8AcqInstrs L) ∧
    hasInstrs P L.swp4RelAddr (swp4RelInstrs L) := by
  simpa [stdStartupExtraChunks, CodeChunks, CodeChunk.holds] using h

private theorem cMainSavedFrame_entails_post (L : StdBinaryLayout) (s_cm : State)
    (stage2Ret w0 w1 w2 w3 wPad : BitVec 64) :
    cMainSavedFrame L s_cm stage2Ret w0 w1 w2 w3 wPad ⊢
      (((s_cm.sp - 0x60#64) - 0x10#64) ↦₆₄ ((s_cm.sp - 0x60#64) + 0x20#64)) ∗
      (((s_cm.sp - 0x60#64) - 0x08#64) ↦₆₄
        (if L.hasArgcGlobal then L.cMainAddr + 0x208#64 else L.cMainAddr + 0x1f4#64)) ∗
      stackAt ((s_cm.sp - 0x60#64) + 0x20#64) 32 ∗
      (((s_cm.sp - 0x60#64) + 0x20#64) ↦₆₄ s_cm.readReg64 (.gpr 29#5)) ∗
      (((s_cm.sp - 0x60#64) + 0x28#64) ↦₆₄ stage2Ret) ∗
      stackAt ((s_cm.sp - 0x60#64) + 0x60#64) 48 := by
  dsimp only [stackAt]
  let u0 := if L.hasArgcGlobal then s_cm.readReg64 (.gpr 24#5) else s_cm.readReg64 (.gpr 23#5)
  let u1 := if L.hasArgcGlobal then s_cm.readReg64 (.gpr 23#5) else wPad
  have hmid : cMainSavedFrame L s_cm stage2Ret w0 w1 w2 w3 wPad =
      ((s_cm.sp - 0x70#64) ↦₆₄ (s_cm.sp - 0x40#64)) ∗
      ((s_cm.sp - 0x68#64) ↦₆₄ (if L.hasArgcGlobal then L.cMainAddr + 0x208#64 else L.cMainAddr + 0x1f4#64)) ∗
      (((s_cm.sp - 0x60#64) ↦₆₄ w0) ∗ ((s_cm.sp - 0x58#64) ↦₆₄ w1) ∗
        ((s_cm.sp - 0x50#64) ↦₆₄ w2) ∗ ((s_cm.sp - 0x48#64) ↦₆₄ w3)) ∗
      ((s_cm.sp - 0x40#64) ↦₆₄ s_cm.readReg64 (.gpr 29#5)) ∗
      ((s_cm.sp - 0x38#64) ↦₆₄ stage2Ret) ∗
      (((s_cm.sp - 0x30#64) ↦₆₄ u0) ∗ ((s_cm.sp - 0x28#64) ↦₆₄ u1) ∗
        ((s_cm.sp - 0x20#64) ↦₆₄ s_cm.readReg64 (.gpr 22#5)) ∗
        ((s_cm.sp - 0x18#64) ↦₆₄ s_cm.readReg64 (.gpr 21#5)) ∗
        ((s_cm.sp - 16#64) ↦₆₄ s_cm.readReg64 (.gpr 20#5)) ∗
        ((s_cm.sp - 8#64) ↦₆₄ s_cm.readReg64 (.gpr 19#5))) := by
    dsimp +zetaDelta only [cMainSavedFrame, u0, u1]; simp only [sepConj_assoc]
  have ha1 : s_cm.sp - 0x60#64 - 0x10#64 = s_cm.sp - 0x70#64 := by bv_lin
  have ha2 : s_cm.sp - 0x60#64 - 0x08#64 = s_cm.sp - 0x68#64 := by bv_lin
  have ha3 : s_cm.sp - 0x60#64 + 0x20#64 = s_cm.sp - 0x40#64 := by bv_lin
  have ha4 : s_cm.sp - 0x60#64 + 0x28#64 = s_cm.sp - 0x38#64 := by bv_lin
  have ha5 : s_cm.sp - 0x60#64 + 0x60#64 = s_cm.sp := by bv_lin
  have hb32 : s_cm.sp - 0x40#64 - BitVec.ofNat 64 32 = s_cm.sp - 0x60#64 := by bv_lin
  have hb48 : s_cm.sp - BitVec.ofNat 64 48 = s_cm.sp - 0x30#64 := by bv_lin
  rw [hmid, ha1, ha2, ha3, ha4, ha5, hb32, hb48]
  have hw4 : (((s_cm.sp - 0x60#64) ↦₆₄ w0) ∗ ((s_cm.sp - 0x58#64) ↦₆₄ w1) ∗
      ((s_cm.sp - 0x50#64) ↦₆₄ w2) ∗ ((s_cm.sp - 0x48#64) ↦₆₄ w3)) ⊢
      memRegion (s_cm.sp - 0x60#64) 32 := by
    have h := pointsToWords64_entails_memRegion [w0, w1, w2, w3] (s_cm.sp - 0x60#64) (by simp)
    simpa only [pointsToWords64_cons, pointsToWords64_nil, sepConj_emp, List.length_cons,
      List.length_nil, show s_cm.sp - 0x60#64 + 8#64 = s_cm.sp - 0x58#64 by bv_lin,
      show s_cm.sp - 0x58#64 + 8#64 = s_cm.sp - 0x50#64 by bv_lin,
      show s_cm.sp - 0x50#64 + 8#64 = s_cm.sp - 0x48#64 by bv_lin] using h
  have hw6 : (((s_cm.sp - 0x30#64) ↦₆₄ u0) ∗ ((s_cm.sp - 0x28#64) ↦₆₄ u1) ∗
      ((s_cm.sp - 0x20#64) ↦₆₄ s_cm.readReg64 (.gpr 22#5)) ∗
      ((s_cm.sp - 0x18#64) ↦₆₄ s_cm.readReg64 (.gpr 21#5)) ∗
      ((s_cm.sp - 16#64) ↦₆₄ s_cm.readReg64 (.gpr 20#5)) ∗
      ((s_cm.sp - 8#64) ↦₆₄ s_cm.readReg64 (.gpr 19#5))) ⊢
      memRegion (s_cm.sp - 0x30#64) 48 := by
    have h := pointsToWords64_entails_memRegion
      [u0, u1, s_cm.readReg64 (.gpr 22#5), s_cm.readReg64 (.gpr 21#5),
       s_cm.readReg64 (.gpr 20#5), s_cm.readReg64 (.gpr 19#5)] (s_cm.sp - 0x30#64) (by simp)
    simpa only [pointsToWords64_cons, pointsToWords64_nil, sepConj_emp, List.length_cons,
      List.length_nil, show s_cm.sp - 0x30#64 + 8#64 = s_cm.sp - 0x28#64 by bv_lin,
      show s_cm.sp - 0x28#64 + 8#64 = s_cm.sp - 0x20#64 by bv_lin,
      show s_cm.sp - 0x20#64 + 8#64 = s_cm.sp - 0x18#64 by bv_lin,
      show s_cm.sp - 0x18#64 + 8#64 = s_cm.sp - 16#64 by bv_lin,
      show s_cm.sp - 16#64 + 8#64 = s_cm.sp - 8#64 by bv_lin] using h
  exact sepConj_mono_right (sepConj_mono_right
    (sepConj_mono hw4 (sepConj_mono_right (sepConj_mono_right hw6))))

private theorem s0_satisfies_initial {L : StdBinaryLayout} {img : ElfImage}
    {inputs : ProcessInputs} {s0 : State}
    (hmatch : L.MatchesImage img = true) (hload : img.loadState inputs = .ok s0)
    (hinfo : InitialStackInfo img inputs s0) (hvalid : inputs.Valid) :
    let sl := StackLayout.of img inputs
    s0.mem ⊨ StdRoConstants L ∗ StdExtraRo L ∗ StdInitGlobals L ∗ StdExtraRw L ∗
      memRegion (sl.sp0 - 0x40000#64) 262144 ∗
      (sl.sp0 ↦₆₄ᵣ BitVec.ofNat 64 inputs.argv.length) ∗
      (sl.argvTableAddr ↦₆₄ᵣ* (sl.argvAddrs ++ [0#64])) ∗
      (sl.envpTableAddr ↦₆₄ᵣ* (sl.envpAddrs ++ [0#64])) ∗
      (sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗
      (sl.randomAddr ↦ₛ inputs.init.auxv.randomBytes) ∗
      (sl.platformAddr ↦ᵣ platformCStringBytes) ∗
      (sl.argvBase ↦ᵣ sl.upperStrBytes) := by
  dsimp only
  have hbrk_le := MatchesImage.brkStart_le hmatch
  have hfl := hinfo.stackBase_floor
  have hhr := hinfo.sp0_headroom.2
  have htop_pos : (StackLayout.of img inputs).sp0.toNat ≤ inputs.init.stackTop.toNat := by
    have := hinfo.addrs_nat; omega
  have h1 := SupportedOn.bupd_intro (MatchesImage.supportedOn_initGlobals_below_brk hmatch hload)
  have h2 := hinfo.stack_supportedOn_bupd hvalid.auxv.random16 (K := 262144) (Nat.le_max_left _ _)
  have h12 := SupportedOn.sepConj_bupd_interval
    (lo := 0) (hi := inputs.init.stackTop.toNat) h1 h2
    (Or.inl (by omega)) ⟨Nat.le_refl _, Nat.zero_le _⟩ ⟨by omega, Nat.le_refl _⟩
  have hsat := MatchesImage.satisfies_roConstants hmatch hload (SupportedOn.satisfies_bupd h12)
  simpa only [BitVec.ofNat_eq_ofNat, sepConj_assoc] using hsat

private theorem satisfies_frame_left {m : Memory} {P A F R : SepProp}
    (hm : m ⊨ P ∗ R) (h : P ⊢ A ∗ F) : m ⊨ A ∗ (F ∗ R) := by
  rw [← sepConj_assoc A F R]
  exact Satisfies.mono (sepConj_mono_left h) hm

private theorem bupd_weaken_frame {m : Memory} {P A A' F R : SepProp}
    (hb : A ⊢ |==> A') (hm : m ⊨ P ∗ R) (h : P ⊢ A ∗ F) : m ⊨ (A' ∗ F) ∗ R := by
  rw [sepConj_assoc A' F R]
  exact Satisfies.of_bupd_frame_left hb (satisfies_frame_left hm h)

private def preTlsSep (L : StdBinaryLayout) (sp0 : BitVec 64) : SepProp :=
  memRegion (sp0 - 0x220#64) 0x60 ∗ (L.phdrAddr ↦ᵣ L.phdrBytes) ∗
    (L.defaultStacksizeAddr ↦₃₂ 0x20000#32) ∗ StdTlsGlobals L ∗ (L.libcAddr ↦₈ 0#8) ∗ StdLibcTlsZero L

private def postTlsSep (L : StdBinaryLayout) (sp0 sysinfoVal : BitVec 64) : SepProp :=
  ((L.builtinTlsAddr + 0xc8#64 - 0xa4#64) ↦₃₂ 0#32) ∗
    ((L.builtinTlsAddr + 0xc8#64 + 0x10#64) ↦₆₄ 0#64) ∗ (L.libcAddr ↦₈ 1#8) ∗
    memRegion (sp0 - 0x220#64) 0x60 ∗ (L.phdrAddr ↦ᵣ L.phdrBytes) ∗
    (L.defaultStacksizeAddr ↦₃₂ 0x20000#32) ∗ StdTlsState L sysinfoVal

private theorem rwAtomListSep_bssAtoms (L : StdBinaryLayout) :
    StdBssGlobals L =
      (L.threadListLockAddr ↦₃₂ 0#32) ∗ (L.sysinfoAddr ↦₆₄ 0#64) ∗ (L.hwcapAddr ↦₆₄ 0#64) ∗
      (L.finalizedAddr ↦₈ 0#8) ∗ (L.initializedAddr ↦₈ 0#8) ∗
      (if L.hasArgcGlobal then L.argcGlobalAddr ↦₆₄ 0#64 else emp) ∗
      (L.argvGlobalAddr ↦₆₄ 0#64) ∗ (L.pageSizeGlobalAddr ↦₆₄ 0#64) ∗
      (L.threadIdCounterAddr ↦₆₄ 0#64) ∗ (L.exitingThreadIdAddr ↦₆₄ 0#64) ∗
      (L.stdDetectCacheAddr ↦₆₄ 0#64) ∗ (L.environAddr ↦₆₄ 0#64) ∗
      (L.prognameAddr ↦₆₄ 0#64) ∗ (L.prognameFullAddr ↦₆₄ 0#64) ∗
      (L.haveLseAtomicsAddr ↦₈ 0#8) ∗ (L.stdinUsedAddr ↦₆₄ 0#64) ∗
      (if L.stdoutUsedAddr == L.stdinUsedAddr then emp else L.stdoutUsedAddr ↦₆₄ 0#64) ∗
      (L.oflHeadAddr ↦₆₄ 0#64) ∗ (L.oflLockAddr ↦₃₂ 0#32) := by
  unfold StdBssGlobals StdBinaryLayout.bssAtoms
  cases L.hasArgcGlobal <;> cases (L.stdoutUsedAddr == L.stdinUsedAddr) <;>
    simp only [↓reduceIte, Bool.false_eq_true,
      List.nil_append, List.cons_append, rwAtomListSep, RwAtom.toSepProp] <;>
    (apply Entails.antisymm <;> sep_entail)

private def initAllSep (L : StdBinaryLayout) (img : ElfImage) (inputs : ProcessInputs) : SepProp :=
  let sl := StackLayout.of img inputs
  StdRoConstants L ∗ StdExtraRo L ∗ StdInitGlobals L ∗ StdExtraRw L ∗
    memRegion (sl.sp0 - 0x40000#64) 262144 ∗
    (sl.sp0 ↦₆₄ᵣ BitVec.ofNat 64 inputs.argv.length) ∗
    (sl.argvTableAddr ↦₆₄ᵣ* (sl.argvAddrs ++ [0#64])) ∗
    (sl.envpTableAddr ↦₆₄ᵣ* (sl.envpAddrs ++ [0#64])) ∗
    (sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗
    (sl.randomAddr ↦ₛ inputs.init.auxv.randomBytes) ∗
    (sl.platformAddr ↦ᵣ platformCStringBytes) ∗
    (sl.argvBase ↦ᵣ sl.upperStrBytes)

theorem startup_to_userMain {P : Program} {L : StdBinaryLayout} {img : ElfImage}
    {inputs : ProcessInputs}
    (c : StdStartupCode P L) (hmatch : L.MatchesImage img = true)
    (hvalid : inputs.Valid) (hrx : L.rxProgram img = P) :
    ∃ s0 s_main : State, ∃ saved_fp : BitVec 64, ∃ R_unused : SepProp,
      img.loadState inputs = .ok s0 ∧
      P.CodeLoaded s0.mem ∧
      LayoutImageFacts L ∧
      Steps P s0 s_main ∧
      StdUserMainState P L img inputs s0 s_main ∧
      let haveLse : BitVec 8 := if inputs.init.auxv.hwcap.getLsbD 8 then 1#8 else 0#8
      let sp_cmain := (StackLayout.of img inputs).sp0 - 0x90#64
      s_main.mem ⊨ StdUserMainPre L img inputs s_main ∗
        (StdPostMainCleanup L haveLse sp_cmain saved_fp ∗ R_unused) := by
  have hwf := MatchesImage.wellFormed hmatch
  have hbrk_eq := MatchesImage.brkStart_eq hmatch
  have hbrk_le := MatchesImage.brkStart_le hmatch
  obtain ⟨s0, hload, hinfo⟩ := loadState_ok_initialStackInfo img hwf hvalid (hbrk_eq ▸ hbrk_le)
  have hL0 : P.CodeLoaded s0.mem := hrx ▸ MatchesImage.codeLoaded hmatch hload
  have lf := extractLayoutImageFacts hmatch hload
  obtain ⟨hc_start, hc_startC, hc_lsm, hc_init, hdummy1, hc_stls, hc_ctls, hc_itp, hset_tp,
    hc_st2, hc_lsi, hinitFn, hc_doInit, hc_getaux, hc_det, hc_ilse, hc_enlse,
    hc_cas8r, hc_cas4a, hc_cas8a, hc_swp4r⟩ := unpack_extra_chunks c.extra
  let sl := StackLayout.of img inputs
  let haveLse : BitVec 8 := if inputs.init.auxv.hwcap.getLsbD 8 then 1#8 else 0#8
  have hsp0_16 := hinfo.sp0_align16
  have hsp0_ge : 262144 ≤ (StackLayout.of img inputs).sp0.toNat := by
    have := hinfo.sp0_headroom.2; omega
  have hscan := auxvScan38_mkAuxvEntries img hvalid.auxv sl.platformAddr sl.randomAddr sl.execfnAddr
  rw [← hinfo.auxvEntries_eq] at hscan
  have hwf_aux := mkAuxvEntries_wf img hvalid.auxv sl.platformAddr sl.randomAddr sl.execfnAddr
  rw [← hinfo.auxvEntries_eq] at hwf_aux
  have hfind_aux := mkAuxvEntries_find? img hvalid.auxv sl.platformAddr sl.randomAddr sl.execfnAddr []
  rw [List.append_nil, ← hinfo.auxvEntries_eq] at hfind_aux
  have hphdr_eq := MatchesImage.phdrVaddr_eq hmatch
  have hphent_eq := (wellFormed_segments_bounds hwf).1
  have hphnum_eq := MatchesImage.phnum_eq hmatch
  have hTlsSpec := staticInitTls_ok hc_stls hc_ctls hc_itp hset_tp c.memOps c.svc_eq
    lf.checkPhdr lf.phdr_end lf.builtinTls_al lf.mainTls_nz
  let sysinfoVal := (auxvScan38 sl.auxvEntries).getD 32 0#64
  have hTls : ∀ (st : State) (FTls : SepProp), st.pc = L.staticInitTlsAddr → st.status = .Running →
      st.sp = sl.sp0 - 0x1c0#64 → st.readReg64 .x0 = sl.sp0 - 0x160#64 →
      st.readReg64 .lr = L.initLibcAddr + 0x10c#64 → StdStatePreserved s0 st →
      SepWP P (L.initLibcAddr + 0x10c#64) st
        ((((sl.sp0 - 0x160#64) ↦₆₄* auxvScan38 sl.auxvEntries) ∗ (L.gotAddr ↦₆₄ 0#64) ∗
          (L.sysinfoAddr ↦₆₄ sysinfoVal) ∗ preTlsSep L sl.sp0) ∗ FTls)
        (fun st' Q => st'.pc = L.initLibcAddr + 0x10c#64 ∧ st'.status = .Running ∧
          st'.sp = sl.sp0 - 0x1c0#64 ∧
          (st'.tpidrEl0 = L.builtinTlsAddr + 0xc8#64 ∧ StdTlsFieldsPreserved st st') ∧
          (Q ⊢ (((sl.sp0 - 0x160#64) ↦₆₄* auxvScan38 sl.auxvEntries) ∗ (L.gotAddr ↦₆₄ 0#64) ∗
            (L.sysinfoAddr ↦₆₄ sysinfoVal) ∗ postTlsSep L sl.sp0 sysinfoVal) ∗ FTls)) := by
    intro st FTls hpct hrunt hspt hx0t hlrt _
    have hsp_al_t : st.spAligned = true := by
      simp only [State.spAligned, hspt, beq_iff_eq]
      have hb : sl.sp0 &&& 15#64 = 0#64 := by
        apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_and]; change sl.sp0.toNat &&& 15 = 0
        rw [Nat.and_two_pow_sub_one_eq_mod _ 4]; exact hsp0_16
      bv_bits
    have hsp_60 : st.sp - 0x60#64 = sl.sp0 - 0x220#64 := by rw [hspt]; bv_lin
    refine SepWP.call_subroutine_frame (ret_pc := L.initLibcAddr + 0x10c#64) hTlsSpec
      (x := (sl.sp0 - 0x160#64, auxvScan38 sl.auxvEntries, 0#8, sysinfoVal)) (F := FTls)
      hpct hrunt hsp_al_t hlrt ?_
      (fun _ _ _ h => not_satisfies_false_sepConj h)
      (fun _ _ _ _ h => not_satisfies_false_sepConj h)
      fun st' hpct' hrunt' hspt' _ => ?_
    · dsimp only [stdStaticInitTlsSpec, preTlsSep]
      rw [hsp_60, pure_sepConj_of_true ⟨hx0t, hphdr_eq ▸ hscan.2.1,
        hphent_eq ▸ hscan.2.2.1, hphnum_eq ▸ hscan.2.2.2.1⟩]
      sep_entail
    · dsimp only [stdStaticInitTlsSpec]
      rw [sepConj_assoc]; apply SepWP.pure_elim; rintro ⟨htp', htls'⟩
      have hspt'' : st'.sp = sl.sp0 - 0x1c0#64 := hspt'.trans hspt
      have hsp'_60 : st'.sp - 0x60#64 = sl.sp0 - 0x220#64 := by rw [hspt'']; bv_lin
      apply SepWP.done hpct' hrunt'
      refine ⟨hpct', hrunt', hspt'', ⟨htp', htls'⟩, ?_⟩
      dsimp only [postTlsSep]; rw [htp', hsp'_60]; sep_entail
  have hLsiSpec : subroutine_ok P L.libcStartInitAddr (stdLibcStartInitSpec L) :=
    libcStartInit_ok P L hc_lsi (initFn_ok P L.initFnAddr hinitFn)
      (initLse_ok P L hc_ilse
        (detectAndInitialize_ok P L hc_det (getauxval_found_ok P L hc_getaux))
        (rustEnableLse_ok P L hc_enlse))
      (doInit_ok P L hc_doInit)
  have hAtomicsNonVm : StdOutlineAtomics (P.withSvc nonVmSvc) L.haveLseAtomicsAddr
      L.cas8RelaxAddr L.cas4AcqAddr L.cas8AcqAddr L.swp4RelAddr :=
    stdOutlineAtomics_of_hasInstrs (P.withSvc nonVmSvc) L
      (hasInstrs_withSvc hc_cas8r) (hasInstrs_withSvc hc_cas4a)
      (hasInstrs_withSvc hc_cas8a) (hasInstrs_withSvc hc_swp4r)
  have hmr_init : memRegion (sl.sp0 - 0x40000#64) 262144 =
      memRegion (sl.sp0 - 0x40000#64) 261600 ∗ memRegion (sl.sp0 - 0x220#64) 0x60 ∗
      memRegion (sl.sp0 - 0x1c0#64) 0x1c0 := by
    have s1 := memRegion_split_le (sl.sp0 - 0x40000#64) 261600 262144 (by decide) (by decide)
    have s2 := memRegion_split_le (sl.sp0 - 0x220#64) 0x60 544 (by decide) (by decide)
    rw [show sl.sp0 - 0x40000#64 + BitVec.ofNat 64 261600 = sl.sp0 - 0x220#64 by bv_lin] at s1
    rw [show sl.sp0 - 0x220#64 + BitVec.ofNat 64 0x60 = sl.sp0 - 0x1c0#64 by bv_lin] at s2
    rw [s1, show (262144 - 261600 : Nat) = 544 from rfl, s2, show (544 - 0x60 : Nat) = 0x1c0 from rfl]
  have hmr_st2 : memRegion (sl.sp0 - 0x40000#64) 261600 ∗ memRegion (sl.sp0 - 0x220#64) 0x60 ∗
      memRegion (sl.sp0 - 0x1c0#64) 0x1c0 =
      stackAt (sl.sp0 - 0x130#64) 261840 ∗ stackFrameAt sl.sp0 0x130 := by
    rw [← hmr_init, ← stackAt_eq_stackFrameAt sl.sp0 0x130]
    have s1 := memRegion_split_le (sl.sp0 - 0x40000#64) 261840 262144 (by decide) (by decide)
    have e1 : sl.sp0 - 0x40000#64 + BitVec.ofNat 64 261840 = sl.sp0 - 0x130#64 := by bv_lin
    have e2 : (sl.sp0 - 0x130#64) - BitVec.ofNat 64 261840 = sl.sp0 - 0x40000#64 := by bv_lin
    dsimp only [stackAt]
    rw [e1] at s1
    rw [e2]
    exact s1
  have hwp_startup : SepWP P L.userMainAddr s0 (initAllSep L img inputs)
      (fun s_main P_out =>
        (s_main.sp = sl.sp0 - 0xa0#64 ∧ s_main.spAligned = true ∧
          261984 ≤ s_main.sp.toNat ∧
          s_main.readReg64 .lr = L.beginShortBacktraceAddr + 0x0c#64 ∧
          s_main.tpidrEl0 = L.builtinTlsAddr + 0xc8#64 ∧
          s_main.fs = initFsState inputs ∧ s_main.trace = [] ∧
          s_main.brk = L.brkStart ∧ s_main.brkStart = L.brkStart ∧
          s_main.physMemAvail = inputs.init.physMemAvail ∧
          ∀ a, s_main.mem.perm a = s0.mem.perm a) ∧
        ∃ saved_fp : BitVec 64, ∃ R_unused : SepProp,
          P_out ⊢ StdUserMainPre L img inputs s_main ∗
            (StdPostMainCleanup L haveLse (sl.sp0 - 0x90#64) saved_fp ∗ R_unused)) := by
    apply SepWP.cut (mid := L.libcStartMainStage2Addr)
    refine SepWP.weaken_pre (P' := (memRegion (sl.sp0 - 0x1c0#64) 0x1c0 ∗ Stage1GlobalsPre L ∗
        StdGotGlobals L ∗ (sl.sp0 ↦₆₄ᵣ BitVec.ofNat 64 inputs.argv.length) ∗
        (sl.argvTableAddr ↦₆₄ᵣ* (sl.argvAddrs ++ [0#64])) ∗
        (sl.envpTableAddr ↦₆₄ᵣ* (sl.envpAddrs ++ [0#64])) ∗
        (sl.auxvTableAddr ↦ₛ encodeAuxvBytes sl.auxvEntries) ∗
        (sl.argvBase ↦ᵣ sl.upperStrBytes) ∗ preTlsSep L sl.sp0) ∗ _) (by
      rw [initAllSep]
      dsimp only [preTlsSep, StdRoConstants, StdInitGlobals, Stage1GlobalsPre,
        StdLibcGlobals, StdDataGlobals, StdLibcTlsZero,
        StdBinaryLayout.libcAtoms, StdBinaryLayout.dataNoStderrAtoms, rwAtomListSep, RwAtom.toSepProp]
      rw [rwAtomListSep_bssAtoms L, hmr_init]
      sep_frame) ?_
    apply SepWP.mono
    case h =>
      exact muslStage1 hinfo hvalid hc_start hc_startC hc_lsm hc_init hdummy1 c.memOps hTls
        (MatchesImage.entry_eq hmatch) c.ne_memset c.ne_tls c.ne_stage2
    case hoom => exact fun _ _ _ ho => ho
    case himp =>
    rintro s_st2 _ hpc_st2 hrun_st2 ⟨⟨hsp_st2, hx0_st2, hx1_st2, hx2_st2,
      st, st', hstd0t, ⟨htp_t', htlst⟩, hstdtf⟩, hent_st2⟩
    apply SepWP.weaken_pre hent_st2
    have hsp_al_st2 : s_st2.spAligned = true := by
      simp only [State.spAligned, hsp_st2, beq_iff_eq]
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_and]; change sl.sp0.toNat &&& 15 = 0
      rw [Nat.and_two_pow_sub_one_eq_mod _ 4]; exact hsp0_16
    have htp_st2 : s_st2.tpidrEl0 = L.builtinTlsAddr + 0xc8#64 := hstdtf.2.2.1.trans htp_t'
    have htlf_0_st2 : StdTlsFieldsPreserved s0 s_st2 :=
      (hstd0t.toTlsFields.trans htlst).trans hstdtf.toTlsFields
    have hm_st2 : memRegion (sl.sp0 - 0x1c0#64) 0x1c0 ∗ memRegion (sl.sp0 - 0x220#64) 0x60 ∗
        memRegion (sl.sp0 - 0x40000#64) 261600 =
        stackAt (sl.sp0 - 0x130#64) 261840 ∗ stackFrameAt sl.sp0 0x130 := by
      rw [← hmr_st2]; apply Entails.antisymm <;> sep_entail
    refine SepWP.weaken_pre (P' := (stdInitGlobalsPre L sl.auxvTableAddr sl.auxvEntries ∗
        stackFrameAt sl.sp0 0x130) ∗ _) (by
      dsimp only [postTlsSep, Stage1GlobalsPost, StdGotGlobals, StdInitFiniGlobals,
        stdInitGlobalsPre, StdBinaryLayout.gotAtoms, StdBinaryLayout.initFiniAtoms,
        rwAtomListSep, RwAtom.toSepProp]
      refine Entails.trans (Q := (memRegion (sl.sp0 - 0x1c0#64) 0x1c0 ∗
        memRegion (sl.sp0 - 0x220#64) 0x60 ∗ memRegion (sl.sp0 - 0x40000#64) 261600) ∗ _)
        (by sep_frame) ?_
      rw [hm_st2]; sep_frame) ?_
    refine stage2_to_cMain P L hc_st2 hLsiSpec hpc_st2 hrun_st2 hsp_st2 hsp_al_st2
      hx0_st2 hx1_st2 hx2_st2 hinfo.argc_bounds.2.1 hvalid.auxv.hwcap_fp_asimd
      (fun t v hm => (hwf_aux.2.2 t v hm).1) hfind_aux.2.2.2.2.2.2.2.2.2.2.1
      hfind_aux.2.2.2.2.2.2.2.2.2.2.2.2.2.1 lf.initArray_bnd
      fun s_cm hpc_cm hrun_cm hsp_cm hsp_al_cm hlr_cm hx0_cm hx1_cm _ hstd_cm => ?_
    dsimp only [stdInitGlobalsPost]
    wp_conv_pre => simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro cacheVal
    refine SepWP.weaken_pre_frame (P' := (L.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ _)
      (fun _ hm => bupd_weaken_frame (pointsTo8_freeze_ro L.haveLseAtomicsAddr haveLse)
        hm (by sep_frame)) ?_
    have hstk_cm : stackAt (sl.sp0 - 0x130#64) 261840 ∗ stackFrameAt (sl.sp0 - 0x30#64) 0x100 =
        stackAt (s_cm.sp - 0x280#64) 261456 ∗ stackAt s_cm.sp 0x280 := by
      rw [← stackAt_eq_stackFrameAt (sl.sp0 - 0x30#64) 0x100, hsp_cm]
      have c1 := memRegion_split_le (sl.sp0 - 0x40000#64) 261840 262096 (by decide) (by decide)
      have c2 := memRegion_split_le (sl.sp0 - 0x40000#64) 261456 262096 (by decide) (by decide)
      rw [show sl.sp0 - 0x40000#64 + BitVec.ofNat 64 261840 = sl.sp0 - 0x130#64 by bv_lin] at c1
      rw [show sl.sp0 - 0x40000#64 + BitVec.ofNat 64 261456 = (sl.sp0 - 0x30#64) - 0x280#64 by bv_lin] at c2
      dsimp only [stackAt]
      rw [show (sl.sp0 - 0x130#64) - 261840#64 = sl.sp0 - 0x40000#64 by bv_lin,
        show (sl.sp0 - 0x30#64) - 256#64 = sl.sp0 - 0x130#64 by bv_lin,
        show ((sl.sp0 - 0x30#64) - 0x280#64) - 261456#64 = sl.sp0 - 0x40000#64 by bv_lin,
        show (sl.sp0 - 0x30#64) - 640#64 = (sl.sp0 - 0x30#64) - 0x280#64 by bv_lin]
      exact c1.symm.trans c2
    have htp_cm : s_cm.tpidrEl0 = L.builtinTlsAddr + 0xc8#64 := hstd_cm.2.2.1.trans htp_st2
    have htlf_0_cm : StdTlsFieldsPreserved s0 s_cm := htlf_0_st2.trans hstd_cm.toTlsFields
    have hsp_cm_lo : 0x280 ≤ s_cm.sp.toNat := by
      rw [hsp_cm, BitVec.toNat_sub_of_le (by
        change 48 ≤ (StackLayout.of img inputs).sp0.toNat; omega)]
      change 640 ≤ (StackLayout.of img inputs).sp0.toNat - 48; omega
    have hsig_cm : s_cm.getSigAction 13#32 = {} := by
      rw [State.getSigAction, htlf_0_cm.2.2.1, hinfo.s0_sigActions]
    have hpoll_cm : evalPpollBytes s_cm.fs stdioPollfdBytes 0 = some (stdioPollfdBytes, 0) := by
      rw [htlf_0_cm.1, hinfo.s0_fs]; exact evalPpollBytes_initFsState inputs
    apply SepWP.of_nonVm c.no_hooks c.svc_eq
    refine step_cMain_preUserMain (stage2Ret := L.libcStartMainStage2Addr + 0x38#64)
      (tp := L.builtinTlsAddr + 0xc8#64) (argvPtr := sl.argvTableAddr)
      (vPage := 0#64) (vArgv := 0#64) (vArgc := 0#64) (argc := inputs.argv.length)
      (haveLse := haveLse) c.langStart.withSvc_nonVm c.memOpsNonVm hAtomicsNonVm lf.al_tid
      (F := _)
      (fun _ hm => satisfies_frame_left hm (by
        refine Entails.trans (Q := (stackAt (sl.sp0 - 0x130#64) 261840 ∗
            stackFrameAt (sl.sp0 - 0x30#64) 0x100) ∗ _) (by sep_frame) ?_
        rw [hstk_cm]; sep_frame))
      hpc_cm hrun_cm hsp_al_cm hsp_cm_lo hlr_cm
      (by cases L.hasArgcGlobal <;> simp [hinfo.argc_bounds.2.1, hx0_cm])
      hx1_cm htp_cm hsig_cm hpoll_cm
      fun s_main w0 w1 w2 w3 wPad hpc_m hrun_m hsp_m hsp_al_m _ hlr_m _ hpre_m => ?_
    apply SepWP.done hpc_m hrun_m
    intro hvm_m
    have hsp_m_eq : s_main.sp = sl.sp0 - 0xa0#64 := by rw [hsp_m, hsp_cm]; bv_lin
    have hsp_m_ge : 261984 ≤ s_main.sp.toNat := by
      rw [hsp_m_eq, BitVec.toNat_sub_of_le (by
        change 160 ≤ (StackLayout.of img inputs).sp0.toNat; omega)]
      change 261984 ≤ (StackLayout.of img inputs).sp0.toNat - 160; omega
    have htp_m : s_main.tpidrEl0 = L.builtinTlsAddr + 0xc8#64 := hpre_m.2.2.1.trans htp_cm
    have hfs_m : s_main.fs = initFsState inputs :=
      hpre_m.1.trans (htlf_0_cm.1.trans hinfo.s0_fs)
    have htr_m : s_main.trace = [] :=
      hpre_m.2.1.trans (htlf_0_cm.2.1.trans hinfo.s0_trace)
    have hbrk_m : s_main.brk = L.brkStart :=
      hvm_m.brk_eq.trans (htlf_0_cm.2.2.2.1.trans (hinfo.s0_brk.trans hbrk_eq))
    have hbrkS_m : s_main.brkStart = L.brkStart :=
      hvm_m.brkStart_eq.trans (htlf_0_cm.2.2.2.2.1.trans (hinfo.s0_brkStart.trans hbrk_eq))
    have hphys_m : s_main.physMemAvail = inputs.init.physMemAvail :=
      hvm_m.physMemAvail_eq.trans (htlf_0_cm.2.2.2.2.2.1.trans hinfo.s0_physMemAvail)
    have hperm_m : ∀ a, s_main.mem.perm a = s0.mem.perm a :=
      fun a => (hvm_m.perm_eq a).trans (htlf_0_cm.2.2.2.2.2.2 a)
    have hstk_m : stackAt (s_cm.sp - 0x280#64) 261456 ∗ stackAt (s_cm.sp - 0x70#64) 0x210 =
        stackAt s_main.sp 261984 := by
      rw [hsp_m_eq, hsp_cm]
      have c := memRegion_split_le (sl.sp0 - 0x40000#64) 261456 261984 (by decide) (by decide)
      rw [show sl.sp0 - 0x40000#64 + BitVec.ofNat 64 261456 = (sl.sp0 - 0x30#64) - 0x280#64 by bv_lin] at c
      dsimp only [stackAt]
      rw [show ((sl.sp0 - 0x30#64) - 0x280#64) - 261456#64 = sl.sp0 - 0x40000#64 by bv_lin,
        show ((sl.sp0 - 0x30#64) - 0x70#64) - 528#64 = (sl.sp0 - 0x30#64) - 0x280#64 by bv_lin,
        show (sl.sp0 - 0xa0#64) - 261984#64 = sl.sp0 - 0x40000#64 by bv_lin]
      exact c.symm
    have hsp_cm_60 : s_cm.sp - 0x60#64 = sl.sp0 - 0x90#64 := by rw [hsp_cm]; bv_lin
    have hsaved := cMainSavedFrame_entails_post L s_cm (L.libcStartMainStage2Addr + 0x38#64)
      w0 w1 w2 w3 wPad
    rw [hsp_cm_60] at hsaved
    exact ⟨⟨hsp_m_eq, hsp_al_m, hsp_m_ge, hlr_m, htp_m, hfs_m, htr_m, hbrk_m, hbrkS_m, hphys_m, hperm_m⟩,
      s_cm.readReg64 (.gpr 29#5), _, by
      refine Entails.trans (Q := ((stackAt (s_cm.sp - 0x280#64) 261456 ∗
          stackAt (s_cm.sp - 0x70#64) 0x210) ∗
        cMainSavedFrame L s_cm (L.libcStartMainStage2Addr + 0x38#64) w0 w1 w2 w3 wPad ∗
        (L.haveLseAtomicsAddr ↦₈ᵣ haveLse) ∗ _))
        (by sep_frame) ?_
      rw [hstk_m, ← pointsTo8RO_dup L.haveLseAtomicsAddr haveLse]
      refine Entails.trans (sepConj_mono_right (sepConj_mono_left hsaved)) ?_
      dsimp only [StdUserMainPre, StdPostMainCleanup, StdCleanupOnceGlobals,
        StdMuslExitGlobalsNoNeedLocks]
      rw [htp_m, show L.builtinTlsAddr + 0xc8#64 + 16#64 = L.builtinTlsAddr + 0xc8#64 + 0x10#64 from rfl]
      sep_frame⟩
  have hm0 : s0.mem ⊨ initAllSep L img inputs ∗ emp := by
    rw [sepConj_emp]; exact s0_satisfies_initial hmatch hload hinfo hvalid
  obtain ⟨s_main, hst1, hres | ⟨_, hfalse⟩⟩ := SepWP.to_reaches_pc hwp_startup hm0 hL0
  · obtain ⟨hpc_m, hrun_m, P_out, hm_out, ⟨hsp_m, hsp_al_m, hsp_ge_m, hlr_m, htp_m, hfs_m,
      htr_m, hbrk_m, hbrkS_m, hphys_m, hperm_m⟩, saved_fp, R_unused, hent_out⟩ := hres
    rw [sepConj_emp] at hm_out
    exact ⟨s0, s_main, saved_fp, R_unused, hload, hL0, lf, hst1,
      ⟨hinfo, hpc_m, hrun_m, hsp_m, hsp_al_m, hsp_ge_m, hlr_m, htp_m, hfs_m, htr_m,
       hbrk_m, hbrkS_m, hphys_m, hperm_m, hst1.codeLoaded hL0⟩,
      Satisfies.mono hent_out hm_out⟩
  · exact False.elim (not_satisfies_false_sepConj hfalse)

end ProofLib.StdStartup
