/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.Process.FsLemmas
public import VerifiedLibraries.Musl.Proofs.MemcpySym
public import VerifiedLibraries.RustStd.Spec.IoCommon
public import VerifiedLibraries.RustStd.Proofs.CoreIo
public import LibsignalBinary.Proofs.SignalSession.CliIo.Sym
public import LibsignalBinary.Proofs.SignalSession.CliIo.MuslOpenDeterministic
public import LibsignalBinary.Proofs.SignalSession.CliIo.ReadLoopCommon
public import LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileSteps
public import LibsignalBinary.Proofs.SignalSession.CliIo.ReadStdinProof

/-!
# Pre-`open` Path Validation and Scalar NUL-Scan Step Lemmas

Proves the pre-`open` segment (`+0x00 .. +0x84`) of `signal_session_io::read_file` (`block[3]`):
1. Pure `cPathOf` ↔ `cstrBytes` and `FsState.fdBytes` bridge lemmas.
2. Induction over the 7-instruction scalar byte copy and interior-NUL scan loop (`+0x54 .. +0x6c`)
   supporting both read-write (`↦ₛ`) and read-only (`↦ᵣ`) path slices.
3. `cliIoReadFile_pre_open`: rejects `4096 ≤ pathBytes.length ∨ 0#8 ∈ pathBytes` with `Err(())` and
   otherwise reaches `+0x84` (`bl open`) with `cstrBytes (cPathOf pathBytes)` at `s0.sp - 8320#64`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileOpenSteps

open Arm64
open Arm64.Obj
open ProofLib
open CryptoVerification (signalSessionIoMultiLib)
open VerifiedLibraries.Musl (memcpySrc)
open VerifiedLibraries.RustStd (
  RustStdAlloc StdErrnoCell stdErrnoAddr vecHeader
  AllocCallPreserved PoolPreserved
  cPathOf rustSepWP_cut rustNz_byte_ze_beq_false
)
open VerifiedLibraries.RustStd.Io (
  SameCpuOracleState allocCallPreserved_of_seg allocCallPreserved_trans
)
open LibsignalBinary.Proofs.SignalSession.CliIo.Sym (
  CliIoPlacement cliIoMpl cliIoPl03 cliIoPC03
  CliIoBlockNoExtern cliIoBlockNoSvc0_03
  sepWP_seg_cliIo_block_pure
  cliIoOpenSym
)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadLoopCommon (
  bv64_beq_ofNat_false bv64_sub_ofNat
  cliIoSavedRegs12 memRegion4096_split_probe32 memRegion4096_refold_probe32
  cliIoReadFile_stack_split vecHeader_to_err_sret
)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileSteps (
  cliIo3_lt cliIoReadFile_open_pc cliIoReadFile_ret_epilogue
)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadStdinProof (
  memRegion24_eq_exists_vecHeader
)

/-! ## 1. Pure `cPathOf` ↔ `cstrBytes` and `FsState.fdBytes` Lemmas -/

private theorem char_ofNat_byte_toNat (b : BitVec 8) :
    (Char.ofNat b.toNat).toNat = b.toNat := by
  have hlt : b.toNat < 256 := b.isLt
  have hval : Nat.isValidChar b.toNat := Or.inl (by omega)
  simp [Char.ofNat, Char.ofNatAux, hval]

theorem toList_cPathOf (bs : List (BitVec 8)) :
    (cPathOf bs).toList = bs.map (fun b => Char.ofNat b.toNat) := by
  simp [cPathOf]

theorem toList_cPathOf_length (bs : List (BitVec 8)) :
    (cPathOf bs).toList.length = bs.length := by
  rw [toList_cPathOf, List.length_map]

theorem mem_toList_cPathOf_lt_256 {bs : List (BitVec 8)} {c : Char}
    (hc : c ∈ (cPathOf bs).toList) : c.toNat < 256 := by
  rw [toList_cPathOf, List.mem_map] at hc
  rcases hc with ⟨b, _, rfl⟩
  rw [char_ofNat_byte_toNat]
  exact b.isLt

theorem cstrBytes_cPathOf (bs : List (BitVec 8)) :
    cstrBytes (cPathOf bs) = bs ++ [0#8] := by
  unfold cstrBytes
  rw [toList_cPathOf, List.map_map]
  congr 1
  have hid : ((fun c : Char => BitVec.ofNat 8 c.toNat) ∘ fun b : BitVec 8 => Char.ofNat b.toNat) = id := by
    funext b
    simp [Function.comp, char_ofNat_byte_toNat]
  rw [hid, List.map_id]

theorem cstrBytes_cPathOf_length (bs : List (BitVec 8)) :
    (cstrBytes (cPathOf bs)).length = bs.length + 1 := by
  rw [cstrBytes_cPathOf, List.length_append, List.length_singleton]

theorem fdBytes_open_localFile {fs : FsState} {path : String} {bs : List (BitVec 8)}
    (hf : fs.files path = some (.file bs)) :
    fs.fdBytes { path := path, accMode := .rdonly, append := false, cloexec := true,
                 offset := 0, kind := .localFile } = bs := by
  simp [FsState.fdBytes, hf]

/-! ## 2. Scalar Byte Copy / Interior-NUL Scan Loop (`+0x54 .. +0x6c`) -/

section
arm64_proof_prelude

private abbrev memcpySrc8 (ro : Bool) (a : BitVec 64) (b : BitVec 8) : SepProp :=
  bif ro then a ↦₈ᵣ b else a ↦₈ b

private theorem memcpySrc_cons (ro : Bool) (a : BitVec 64) (b : BitVec 8) (bs : List (BitVec 8)) :
    memcpySrc ro a (b :: bs) = (memcpySrc8 ro a b ∗ memcpySrc ro (a + 1#64) bs) := by
  cases ro <;> simp [memcpySrc, memcpySrc8]

private theorem memcpySrc_singleton (ro : Bool) (a : BitVec 64) (b : BitVec 8) :
    memcpySrc ro a [b] = memcpySrc8 ro a b := by
  cases ro <;> simp [memcpySrc, memcpySrc8]

private structure FileScanPreserved (s0 s1 : State) : Prop where
  run_eq : s1.status = .Running
  sp_eq : s1.sp = s0.sp
  spAligned_eq : s1.spAligned = true
  fs_eq : s1.fs = s0.fs
  trace_eq : s1.trace = s0.trace
  sig_eq : s1.sigActions = s0.sigActions
  tp_eq : s1.tpidrEl0 = s0.tpidrEl0
  bs_eq : s1.brkStart = s0.brkStart
  oracle_eq : s1.oracle = s0.oracle
  symtab_eq : s1.symtab = s0.symtab
  lr_eq : s1.readReg64 .lr = s0.readReg64 .lr
  x1_eq : s1.readReg64 .x1 = s0.readReg64 .x1
  x8_eq : s1.readReg64 .x8 = s0.readReg64 .x8
  x29_eq : s1.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5)
  vregs_eq : calleeSavedVRegs s1 = calleeSavedVRegs s0

private theorem FileScanPreserved.trans {s0 s1 s2 : State}
    (h01 : FileScanPreserved s0 s1) (h12 : FileScanPreserved s1 s2) :
    FileScanPreserved s0 s2 :=
  ⟨h12.run_eq, h12.sp_eq.trans h01.sp_eq, h12.spAligned_eq,
   h12.fs_eq.trans h01.fs_eq, h12.trace_eq.trans h01.trace_eq,
   h12.sig_eq.trans h01.sig_eq, h12.tp_eq.trans h01.tp_eq,
   h12.bs_eq.trans h01.bs_eq, h12.oracle_eq.trans h01.oracle_eq,
   h12.symtab_eq.trans h01.symtab_eq, h12.lr_eq.trans h01.lr_eq,
   h12.x1_eq.trans h01.x1_eq, h12.x8_eq.trans h01.x8_eq,
   h12.x29_eq.trans h01.x29_eq, h12.vregs_eq.trans h01.vregs_eq⟩

private theorem FileScanPreserved.trans_right {s0 s1 s2 : State}
    (h12 : FileScanPreserved s1 s2) (h01 : FileScanPreserved s0 s1) :
    FileScanPreserved s0 s2 :=
  h01.trans h12

private theorem cliIoReadFile_nul_scan_loop [CliIoPlacement] {ro : Bool} {tgt : BitVec 64}
    {post : State → SepProp → Prop}
    (rem : List (BitVec 8)) {idx n : Nat} {pathPtr dst scratchPtr : BitVec 64}
    {F : SepProp} {s : State} {sc0 : BitVec 8}
    (h1 : 1 ≤ rem.length) (hsum : idx + rem.length = n) (hn : n < 4096)
    (hpc : s.pc = cliIoPl03.base + 84#64) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = pathPtr + BitVec.ofNat 64 idx)
    (hx9 : s.readReg64 (.gpr 9#5) = scratchPtr)
    (hx10 : s.readReg64 (.gpr 10#5) = dst + BitVec.ofNat 64 idx)
    (hx12 : s.readReg64 (.gpr 12#5) = BitVec.ofNat 64 rem.length)
    (hfound : ∀ sf : State, ∀ sc1 : BitVec 8, sf.pc = cliIoPl03.base + 52#64 →
      FileScanPreserved s sf → 0#8 ∈ rem →
      SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) tgt sf
        (memcpySrc ro (pathPtr + BitVec.ofNat 64 idx) rem ∗
          memRegion (dst + BitVec.ofNat 64 idx) (4096 - idx) ∗
          (scratchPtr ↦₈ sc1) ∗ F) post)
    (hnone : ∀ sf : State, ∀ sc1 : BitVec 8, sf.pc = cliIoPl03.base + 112#64 →
      FileScanPreserved s sf → (∀ b ∈ rem, b ≠ 0#8) →
      SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) tgt sf
        (memcpySrc ro (pathPtr + BitVec.ofNat 64 idx) rem ∗
          ((dst + BitVec.ofNat 64 idx) ↦ₛ rem) ∗
          memRegion (dst + BitVec.ofNat 64 n) (4096 - n) ∗
          (scratchPtr ↦₈ sc1) ∗ F) post) :
    SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) tgt s
      (memcpySrc ro (pathPtr + BitVec.ofNat 64 idx) rem ∗
        memRegion (dst + BitVec.ofNat 64 idx) (4096 - idx) ∗
        (scratchPtr ↦₈ sc0) ∗ F) post := by
  induction rem generalizing idx F s sc0 with
  | nil => simp at h1
  | cons b rem' ih =>
    by_cases hb0 : b = 0#8
    · subst hb0
      wp_conv_pre => rw [memcpySrc_cons]; simp only [sepConj_assoc]
      apply rustSepWP_cut (mid := cliIoPl03.base + 52#64)
      cases ro <;>
      · dsimp only [memcpySrc, memcpySrc8, cond] at hfound ⊢
        wp_sym_steps
        refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun) ?_
        refine SepWP.weaken_pre ?_
          (hfound _ 0#8 (by simp [arm64_norm])
            ⟨by simpa [arm64_norm] using hrun, by simp [arm64_norm],
             by simpa [arm64_norm] using hsp, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
             by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
             by simp [arm64_norm], by simp [arm64_norm, calleeSavedVRegs]⟩
            (List.mem_cons_self ..))
        simp only [pointsToBytes_cons, pointsToBytesRO_cons, bv_lin_norm]
        sep_entail
    · obtain ⟨hb1, hb2, hb3⟩ := rustNz_byte_ze_beq_false hb0
      wp_conv_pre =>
        rw [show 4096 - idx = (4095 - idx) + 1 by simp at hsum; omega,
          memRegion_succ_off dst idx (4095 - idx) (by simp at hsum; omega)]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWP.exists_left; intro z_dst
      rcases rem' with _ | ⟨b2, rest⟩
      · have hlen1 : ([b] : List (BitVec 8)).length = 1 := rfl
        rw [hlen1] at hx12
        wp_conv_pre => rw [memcpySrc_singleton]
        apply rustSepWP_cut (mid := cliIoPl03.base + 112#64)
        cases ro <;>
        · dsimp only [memcpySrc, memcpySrc8, cond] at hnone ⊢
          wp_sym_steps
          refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun) ?_
          refine SepWP.weaken_pre ?_
            (hnone _ b (by simp [arm64_norm])
              ⟨by simpa [arm64_norm] using hrun, by simp [arm64_norm],
               by simpa [arm64_norm] using hsp, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
               by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
               by simp [arm64_norm], by simp [arm64_norm, calleeSavedVRegs]⟩
              (by intro x hx; simp at hx; subst hx; exact hb0))
          rw [show n = idx + 1 by simp at hsum; omega,
            show 4096 - (idx + 1) = 4095 - idx by omega]
          simp only [pointsToBytes_singleton, pointsToBytesRO_singleton, bv_lin_norm]
          sep_entail
      · have hlen_cons_lt : (b :: b2 :: rest).length < 4096 := by
          simp only [List.length_cons] at hsum ⊢; omega
        have hsub1 : BitVec.ofNat 64 (b :: b2 :: rest).length - 1#64 =
            BitVec.ofNat 64 (b2 :: rest).length :=
          bv64_sub_ofNat (b := 1) (by simp)
        have hne1 : (BitVec.ofNat 64 (b :: b2 :: rest).length != 1#64) = true := by
          rw [bne_iff_ne]
          intro heq
          have hto := congrArg BitVec.toNat heq
          simp only [BitVec.toNat_ofNat, List.length_cons] at hto hlen_cons_lt
          omega
        have hp_add1 : pathPtr + BitVec.ofNat 64 idx + 1#64 =
            pathPtr + BitVec.ofNat 64 (idx + 1) := by rw [BitVec.ofNat_add]; bv_lin
        have hd_add1 : dst + BitVec.ofNat 64 idx + 1#64 =
            dst + BitVec.ofNat 64 (idx + 1) := by rw [BitVec.ofNat_add]; bv_lin
        let DstHead : SepProp := (dst + BitVec.ofNat 64 idx) ↦₈ b
        wp_conv_pre => rw [memcpySrc_cons]; simp only [sepConj_assoc]
        apply rustSepWP_cut (mid := cliIoPl03.base + 84#64)
        cases ro
        · dsimp only [memcpySrc8, cond]
          wp_sym_steps
          refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun) ?_
          let SrcHead : SepProp := (pathPtr + BitVec.ofNat 64 idx) ↦₈ b
          refine SepWP.weaken_pre
            (P' := memcpySrc false (pathPtr + BitVec.ofNat 64 (idx + 1)) (b2 :: rest) ∗
              memRegion (dst + BitVec.ofNat 64 (idx + 1)) (4096 - (idx + 1)) ∗
              (scratchPtr ↦₈ b) ∗ (SrcHead ∗ DstHead ∗ F))
            (by dsimp only [SrcHead, DstHead]
                rw [show 4096 - (idx + 1) = 4095 - idx by omega, ← hp_add1, ← hd_add1]
                sep_entail)
            (ih (idx := idx + 1) (F := SrcHead ∗ DstHead ∗ F) (sc0 := b)
              (by simp) (by simp only [List.length_cons] at hsum ⊢; omega)
              (by simp [arm64_norm])
              (by simpa [arm64_norm] using hrun)
              (by simpa [arm64_norm] using hsp)
              (by rw [← hp_add1]; simp only [arm64_norm])
              (by simpa [arm64_norm] using hx9)
              (by rw [← hd_add1]; simp only [arm64_norm])
              (by simp only [arm64_norm])
              (fun sf sc1 hpc_f hpres2 hmem_rest =>
                SepWP.weaken_pre ?_
                  (hfound sf sc1 hpc_f
                    (hpres2.trans_right
                      ⟨by simpa [arm64_norm] using hrun, by simp [arm64_norm],
                       by simpa [arm64_norm] using hsp, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                       by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
                       by simp [arm64_norm], by simp [arm64_norm, calleeSavedVRegs]⟩)
                    (List.mem_cons_of_mem b hmem_rest)))
              (fun sf sc1 hpc_f hpres2 hno_rest =>
                SepWP.weaken_pre ?_
                  (hnone sf sc1 hpc_f
                    (hpres2.trans_right
                      ⟨by simpa [arm64_norm] using hrun, by simp [arm64_norm],
                       by simpa [arm64_norm] using hsp, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                       by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
                       by simp [arm64_norm], by simp [arm64_norm, calleeSavedVRegs]⟩)
                    (by intro x hx; rcases List.mem_cons.mp hx with rfl | hxr
                        · exact hb0
                        · exact hno_rest x hxr))))
          · have hmerge_dst :
                DstHead ∗ memRegion (dst + BitVec.ofNat 64 (idx + 1)) (4096 - (idx + 1)) ⊢
                  memRegion (dst + BitVec.ofNat 64 idx) (4096 - idx) := by
              dsimp only [DstHead]
              rw [← hd_add1,
                show 4096 - (idx + 1) = 4095 - idx by omega,
                show 4096 - idx = (4095 - idx) + 1 by simp only [List.length_cons] at hsum; omega]
              exact memRegion_byte_merge (dst + BitVec.ofNat 64 idx) b (4095 - idx)
                (by simp only [List.length_cons] at hsum; omega)
            rw [memcpySrc_cons (b := b) (bs := b2 :: rest), hp_add1]
            dsimp only [memcpySrc8, cond]
            let KeepFound : SepProp :=
              SrcHead ∗ memcpySrc false (pathPtr + BitVec.ofNat 64 (idx + 1)) (b2 :: rest) ∗
                (scratchPtr ↦₈ sc1) ∗ F
            refine Entails.trans ?_
              (Entails.trans (sepConj_mono_left (Q := KeepFound) hmerge_dst)
                (by dsimp only [KeepFound, SrcHead]; sep_entail))
            dsimp only [KeepFound, SrcHead]; sep_entail
          · rw [memcpySrc_cons (b := b) (bs := b2 :: rest), pointsToBytes_cons_off dst idx b (b2 :: rest), hp_add1]
            dsimp only [memcpySrc8, cond, SrcHead, DstHead]; sep_entail
        · dsimp only [memcpySrc8, cond]
          wp_sym_steps
          refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun) ?_
          let SrcHead : SepProp := (pathPtr + BitVec.ofNat 64 idx) ↦₈ᵣ b
          refine SepWP.weaken_pre
            (P' := memcpySrc true (pathPtr + BitVec.ofNat 64 (idx + 1)) (b2 :: rest) ∗
              memRegion (dst + BitVec.ofNat 64 (idx + 1)) (4096 - (idx + 1)) ∗
              (scratchPtr ↦₈ b) ∗ (SrcHead ∗ DstHead ∗ F))
            (by dsimp only [SrcHead, DstHead]
                rw [show 4096 - (idx + 1) = 4095 - idx by omega, ← hp_add1, ← hd_add1]
                sep_entail)
            (ih (idx := idx + 1) (F := SrcHead ∗ DstHead ∗ F) (sc0 := b)
              (by simp) (by simp only [List.length_cons] at hsum ⊢; omega)
              (by simp [arm64_norm])
              (by simpa [arm64_norm] using hrun)
              (by simpa [arm64_norm] using hsp)
              (by rw [← hp_add1]; simp only [arm64_norm])
              (by simpa [arm64_norm] using hx9)
              (by rw [← hd_add1]; simp only [arm64_norm])
              (by simp only [arm64_norm])
              (fun sf sc1 hpc_f hpres2 hmem_rest =>
                SepWP.weaken_pre ?_
                  (hfound sf sc1 hpc_f
                    (hpres2.trans_right
                      ⟨by simpa [arm64_norm] using hrun, by simp [arm64_norm],
                       by simpa [arm64_norm] using hsp, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                       by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
                       by simp [arm64_norm], by simp [arm64_norm, calleeSavedVRegs]⟩)
                    (List.mem_cons_of_mem b hmem_rest)))
              (fun sf sc1 hpc_f hpres2 hno_rest =>
                SepWP.weaken_pre ?_
                  (hnone sf sc1 hpc_f
                    (hpres2.trans_right
                      ⟨by simpa [arm64_norm] using hrun, by simp [arm64_norm],
                       by simpa [arm64_norm] using hsp, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                       by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
                       by simp [arm64_norm], by simp [arm64_norm, calleeSavedVRegs]⟩)
                    (by intro x hx; rcases List.mem_cons.mp hx with rfl | hxr
                        · exact hb0
                        · exact hno_rest x hxr))))
          · have hmerge_dst :
                DstHead ∗ memRegion (dst + BitVec.ofNat 64 (idx + 1)) (4096 - (idx + 1)) ⊢
                  memRegion (dst + BitVec.ofNat 64 idx) (4096 - idx) := by
              dsimp only [DstHead]
              rw [← hd_add1,
                show 4096 - (idx + 1) = 4095 - idx by omega,
                show 4096 - idx = (4095 - idx) + 1 by simp only [List.length_cons] at hsum; omega]
              exact memRegion_byte_merge (dst + BitVec.ofNat 64 idx) b (4095 - idx)
                (by simp only [List.length_cons] at hsum; omega)
            rw [memcpySrc_cons (b := b) (bs := b2 :: rest), hp_add1]
            dsimp only [memcpySrc8, cond]
            let KeepFound : SepProp :=
              SrcHead ∗ memcpySrc true (pathPtr + BitVec.ofNat 64 (idx + 1)) (b2 :: rest) ∗
                (scratchPtr ↦₈ sc1) ∗ F
            refine Entails.trans ?_
              (Entails.trans (sepConj_mono_left (Q := KeepFound) hmerge_dst)
                (by dsimp only [KeepFound, SrcHead]; sep_entail))
            dsimp only [KeepFound, SrcHead]; sep_entail
          · rw [memcpySrc_cons (b := b) (bs := b2 :: rest), pointsToBytes_cons_off dst idx b (b2 :: rest), hp_add1]
            dsimp only [memcpySrc8, cond, SrcHead, DstHead]; sep_entail

/-! ## 3. Full Pre-`open` Segment (`+0x00 .. +0x84`, Including Early Rejects) -/

/-- Step `read_file` (`block[3]`) from entry `+0x00`:
    - if `4096 ≤ pathBytes.length ∨ 0#8 ∈ pathBytes`, writes `-1` to `[sret]` and returns cleanly via
      `+0x208 .. +0x228` with `fs`, `trace`, `memcpySrc`, `StdErrnoCell`, and `A.pool lb lk` intact;
    - if `pathBytes.length < 4096 ∧ 0#8 ∉ pathBytes`, reaches `+0x84` (`bl open`) with
      `(s0.sp - 8320#64) ↦ₛ cstrBytes (cPathOf pathBytes)` ready on the stack. -/
theorem cliIoReadFile_pre_open [CliIoPlacement]
    {oom : State → State → Prop} (A : RustStdAlloc oom)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    {ro : Bool} {s0 : State} {sret pathPtr : BitVec 64} {pathBytes : List (BitVec 8)}
    {stackBytes lb lk : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 8320 ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hcl0 : signalSessionIoMultiLib.CodeLoaded cliIoMpl s0.mem)
    (hpc0 : s0.pc = cliIoPl03.base) (hrun0 : s0.status = .Running) (hsp0 : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = pathPtr)
    (hx1 : (s0.readReg64 .x1).toNat = pathBytes.length)
    (hx8 : s0.readReg64 .x8 = sret)
    (herr_early : (4096 ≤ pathBytes.length ∨ 0#8 ∈ pathBytes) →
      ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
        signalSessionIoMultiLib.CodeLoaded cliIoMpl sf.mem →
        AllocCallPreserved s0 sf →
        ∀ {Pre_f : SepProp},
          (Pre_f ⊢ stackAt s0.sp stackBytes ∗
            (((sret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (sret + 8#64) 16) ∗
              memcpySrc ro pathPtr pathBytes ∗ StdErrnoCell s0.tpidrEl0) ∗
            A.pool lb lk sf) →
          post sf Pre_f)
    (hat_open : pathBytes.length < 4096 → 0#8 ∉ pathBytes →
      ∀ (sm : State) (ev0 : BitVec 32) (v0 v1 v2 st0 st1 st2 st3 : BitVec 64),
        signalSessionIoMultiLib.CodeLoaded cliIoMpl sm.mem →
        sm.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoOpenSym →
        sm.status = .Running →
        sm.sp = s0.sp - 8320#64 →
        sm.spAligned = true →
        sm.readReg64 .lr = cliIoPl03.base + 136#64 →
        sm.readReg64 .x0 = s0.sp - 8320#64 →
        sm.readReg32 .x1 = O_CLOEXEC_W32 →
        sm.readReg64 (.gpr 24#5) = sret →
        sm.readReg64 (.gpr 29#5) = s0.sp - 96#64 →
        calleeSavedVRegs sm = calleeSavedVRegs s0 →
        AllocCallPreserved s0 sm →
        SepWP P (s0.readReg64 .lr) sm
          (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
            ((s0.sp - 8320#64) ↦ₛ cstrBytes (cPathOf pathBytes)) ∗
            memRegion ((s0.sp - 8320#64) + BitVec.ofNat 64 (pathBytes.length + 1))
              (4095 - pathBytes.length) ∗
            memRegion (s0.sp - 4224#64) 4096 ∗
            vecHeader (s0.sp - 128#64) st0 st1 st2 ∗
            ((s0.sp - 104#64) ↦₆₄ st3) ∗
            cliIoSavedRegs12 s0 ∗
            memcpySrc ro pathPtr pathBytes ∗
            vecHeader sret v0 v1 v2 ∗
            (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev0) ∗
            A.pool lb lk sm)
          post oomProp) :
    SepWP P (s0.readReg64 .lr) s0
      (stackAt s0.sp stackBytes ∗ memcpySrc ro pathPtr pathBytes ∗
        memRegion sret 24 ∗ StdErrnoCell s0.tpidrEl0 ∗ A.pool lb lk s0)
      post oomProp := by
  have hlen_lt64 : pathBytes.length < 2 ^ 64 := hx1 ▸ (s0.readReg64 .x1).isLt
  have hx1_bv : s0.readReg64 .x1 = BitVec.ofNat 64 pathBytes.length := by
    rw [← hx1]; simp
  wp_conv_pre =>
    dsimp only [StdErrnoCell]
    rw [cliIoReadFile_stack_split s0.sp hlo hhi,
      memRegion24_eq_exists_vecHeader sret,
      memRegion4096_split_probe32 (s0.sp - 8320#64),
      memRegion4096_split_probe32 (s0.sp - 4224#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, bv_lin_norm]
  refine SepWP.exists_elim fun ev0 =>
    SepWP.exists_elim fun v0 => SepWP.exists_elim fun v1 =>
    SepWP.exists_elim fun v2 =>
    SepWP.exists_elim fun st0 => SepWP.exists_elim fun st1 =>
    SepWP.exists_elim fun st2 => SepWP.exists_elim fun st3 =>
    SepWP.exists_elim fun r0 => SepWP.exists_elim fun r1 =>
    SepWP.exists_elim fun r2 => SepWP.exists_elim fun r3 =>
    SepWP.exists_elim fun r4 => SepWP.exists_elim fun r5 =>
    SepWP.exists_elim fun r6 => SepWP.exists_elim fun r7 =>
    SepWP.exists_elim fun r8 => SepWP.exists_elim fun r9 =>
    SepWP.exists_elim fun r10 => SepWP.exists_elim fun r11 =>
    SepWP.exists_elim fun wp4224 => SepWP.exists_elim fun wp8320 => ?_
  have hrefold8320 :
      memRegion (s0.sp - 8320#64) 32 ∗ ((s0.sp - 8288#64) ↦₆₄ 0#64) ∗
        memRegion (s0.sp - 8280#64) 4056 ⊢ memRegion (s0.sp - 8320#64) 4096 := by
    simpa only [bv_lin_norm] using memRegion4096_refold_probe32 (s0.sp - 8320#64) 0#64
  have hrefold4224 :
      memRegion (s0.sp - 4224#64) 32 ∗ ((s0.sp - 4192#64) ↦₆₄ 0#64) ∗
        memRegion (s0.sp - 4184#64) 4056 ⊢ memRegion (s0.sp - 4224#64) 4096 := by
    simpa only [bv_lin_norm] using memRegion4096_refold_probe32 (s0.sp - 4224#64) 0#64
  rcases le_or_gt 4096 pathBytes.length with hge | hlt
  · have hule_f : BitVec.ule (BitVec.ofNat 64 pathBytes.length) 4095#64 = false := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have hult_t : BitVec.ult 4095#64 (BitVec.ofNat 64 pathBytes.length) = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl0
      (mid := cliIoPl03.base + 520#64)
    intro s1' hcpu1_0; have hcpu1 := hcpu1_0.1
    change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
    have hpc1' : s1'.pc = cliIoPl03.base := hcpu1.pc_eq.trans hpc0
    have hrun1' : s1'.status = .Running := hcpu1.status_eq.trans hrun0
    have hsp1_in : s1'.sp = s0.sp := hcpu1.sp_eq
    have hsp1' : s1'.spAligned = true := by rw [hcpu1.spAligned]; exact hsp0
    have hx1_1' : s1'.readReg64 .x1 = BitVec.ofNat 64 pathBytes.length := (hcpu1.readReg64 .x1).trans hx1_bv
    have hx8_1' : s1'.readReg64 .x8 = sret := (hcpu1.readReg64 .x8).trans hx8
    wp_conv_pre =>
      rw [show vecHeader sret v0 v1 v2 =
        (sret ↦₆₄ v0) ∗ ((sret + 8#64) ↦₆₄ v1) ∗ ((sret + 16#64) ↦₆₄ v2) from rfl]
      simp only [sepConj_assoc]
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun1')
      fun se hcpu_e0 hcl_e hnsp_e hsym_e => ?_
    have hcpu_e := hcpu_e0.1
    have ⟨hacp_0e, hpool_0e⟩ :=
      allocCallPreserved_of_seg hcpu1_0 hcpu_e0 hnsp_e hsym_e
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
    have hpool_eq : A.pool lb lk s0 = A.pool lb lk se := (A.pool_transport _ _ s0 se hpool_0e).symm
    refine SepWP.weaken_pre ?_
      (cliIoReadFile_ret_epilogue A hext3 (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3)
        (R_out := ((sret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (sret + 8#64) 16) ∗
          memcpySrc ro pathPtr pathBytes ∗ StdErrnoCell s0.tpidrEl0)
        (lb_f := lb) (lk_f := lk)
        hlo hhi hcl_e (hcpu_e.pc_eq.trans (by simp [arm64_norm]))
        (hcpu_e.status_eq.trans hrun1') hsp0 (hcpu_e.sp_eq.trans (by simp [arm64_norm]))
        (hcpu_e.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs s1').trans hcpu1.calleeSavedVRegs))
        fun sf hpc_f hrun_f hsp_f hcs_f hcl_f hacp_ef _ hent =>
          herr_early (Or.inl hge) sf hpc_f hrun_f hsp_f hcs_f hcl_f
            (allocCallPreserved_trans hacp_0e hacp_ef) hent)
    have herr_sret :
        (sret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ ((sret + 8#64) ↦₆₄ v1) ∗ ((sret + 16#64) ↦₆₄ v2) ⊢
          (sret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (sret + 8#64) 16 :=
      vecHeader_to_err_sret sret v1 v2
    have hev_cell : (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev0) ⊢ StdErrnoCell s0.tpidrEl0 :=
      Entails.sepExists_right ev0 (Entails.refl _)
    rw [hpool_eq,
      hcpu1.readReg64 (.gpr 29#5), hcpu1.readReg64 (.gpr 30#5),
      hcpu1.readReg64 (.gpr 28#5), hcpu1.readReg64 (.gpr 27#5),
      hcpu1.readReg64 (.gpr 26#5), hcpu1.readReg64 (.gpr 25#5),
      hcpu1.readReg64 (.gpr 24#5), hcpu1.readReg64 (.gpr 23#5),
      hcpu1.readReg64 (.gpr 22#5), hcpu1.readReg64 (.gpr 21#5),
      hcpu1.readReg64 (.gpr 20#5), hcpu1.readReg64 (.gpr 19#5)]
    dsimp only [cliIoSavedRegs12]; simp only [bv_lin_norm]
    let KeepE : SepProp :=
      stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        (((s0.sp - 96#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
          ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
          ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 28#5)) ∗
          ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (.gpr 27#5)) ∗
          ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗
          ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
          ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
          ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5))) ∗
        memcpySrc ro pathPtr pathBytes ∗ A.pool lb lk se
    refine Entails.trans ?_
      (Entails.trans
        (sepConj_mono hrefold8320 (sepConj_mono hrefold4224
          (sepConj_mono herr_sret (sepConj_mono_left (Q := KeepE) hev_cell))))
        (by dsimp only [KeepE]; sep_entail))
    dsimp only [KeepE]; sep_entail
  · have hule_t : BitVec.ule (BitVec.ofNat 64 pathBytes.length) 4095#64 = true := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
    have hult_f : BitVec.ult 4095#64 (BitVec.ofNat 64 pathBytes.length) = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    by_cases hnul : 0#8 ∈ pathBytes
    · have h1_pos : 1 ≤ pathBytes.length := by
        cases pathBytes with
        | nil => simp at hnul
        | cons _ _ => simp
      have hnez_len : (BitVec.ofNat 64 pathBytes.length == 0#64) = false :=
        bv64_beq_ofNat_false (b := 0) (by omega) (by omega) (by decide)
      apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl0
        (mid := cliIoPl03.base + 520#64)
      intro s1' hcpu1_0; have hcpu1 := hcpu1_0.1
      change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
      have hpc1' : s1'.pc = cliIoPl03.base := hcpu1.pc_eq.trans hpc0
      have hrun1' : s1'.status = .Running := hcpu1.status_eq.trans hrun0
      have hsp1_in : s1'.sp = s0.sp := hcpu1.sp_eq
      have hsp1' : s1'.spAligned = true := by rw [hcpu1.spAligned]; exact hsp0
      have hx0_1' : s1'.readReg64 .x0 = pathPtr := (hcpu1.readReg64 .x0).trans hx0
      have hx1_1' : s1'.readReg64 .x1 = BitVec.ofNat 64 pathBytes.length := (hcpu1.readReg64 .x1).trans hx1_bv
      have hx8_1' : s1'.readReg64 .x8 = sret := (hcpu1.readReg64 .x8).trans hx8
      apply rustSepWP_cut (mid := cliIoPl03.base + 84#64)
      wp_sym_steps
      refine SepWP.done (by simp [arm64_norm])
        (by simpa [arm64_norm] using hrun1') ?_
      let F_nul : SepProp :=
        memRegion (s0.sp - 4223#64) 4095 ∗
          stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
          vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
          (((s0.sp - 96#64) ↦₆₄ s1'.readReg64 (.gpr 29#5)) ∗
            ((s0.sp - 88#64) ↦₆₄ s1'.readReg64 (.gpr 30#5)) ∗
            ((s0.sp - 80#64) ↦₆₄ s1'.readReg64 (.gpr 28#5)) ∗
            ((s0.sp - 72#64) ↦₆₄ s1'.readReg64 (.gpr 27#5)) ∗
            ((s0.sp - 64#64) ↦₆₄ s1'.readReg64 (.gpr 26#5)) ∗
            ((s0.sp - 56#64) ↦₆₄ s1'.readReg64 (.gpr 25#5)) ∗
            ((s0.sp - 48#64) ↦₆₄ s1'.readReg64 (.gpr 24#5)) ∗
            ((s0.sp - 40#64) ↦₆₄ s1'.readReg64 (.gpr 23#5)) ∗
            ((s0.sp - 32#64) ↦₆₄ s1'.readReg64 (.gpr 22#5)) ∗
            ((s0.sp - 24#64) ↦₆₄ s1'.readReg64 (.gpr 21#5)) ∗
            ((s0.sp - 16#64) ↦₆₄ s1'.readReg64 (.gpr 20#5)) ∗
            ((s0.sp - 8#64) ↦₆₄ s1'.readReg64 (.gpr 19#5))) ∗
          vecHeader sret v0 v1 v2 ∗ (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev0) ∗ A.pool lb lk s0
      have hcarve4224 :
          memRegion (s0.sp - 4224#64) 4096 =
            ((∃∗ sc0 : BitVec 8, (s0.sp - 4224#64) ↦₈ sc0) ∗ memRegion (s0.sp - 4223#64) 4095) := by
        simpa only [bv_lin_norm] using memRegion_succ_off (s0.sp - 4224#64) 0 4095 (by decide)
      refine SepWP.weaken_pre
        (P' := memcpySrc ro (pathPtr + 0#64) pathBytes ∗
          memRegion ((s0.sp - 8320#64) + 0#64) 4096 ∗
          (∃∗ sc0 : BitVec 8, (s0.sp - 4224#64) ↦₈ sc0) ∗ F_nul) ?_ ?_
      · dsimp only [F_nul]; simp only [← sepConj_assoc]; rw [sepConj_assoc]
        have hcarve4224' :
            memRegion (s0.sp - 4224#64) 4096 ⊢
              (∃∗ sc0 : BitVec 8, (s0.sp - 4224#64) ↦₈ sc0) ∗ memRegion (s0.sp - 4223#64) 4095 := by
          rw [hcarve4224]; exact Entails.refl _
        simp only [bv_lin_norm]
        let KeepN0 : SepProp :=
          memcpySrc ro pathPtr pathBytes ∗
            stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
            vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
            (((s0.sp - 96#64) ↦₆₄ s1'.readReg64 (.gpr 29#5)) ∗
              ((s0.sp - 88#64) ↦₆₄ s1'.readReg64 (.gpr 30#5)) ∗
              ((s0.sp - 80#64) ↦₆₄ s1'.readReg64 (.gpr 28#5)) ∗
              ((s0.sp - 72#64) ↦₆₄ s1'.readReg64 (.gpr 27#5)) ∗
              ((s0.sp - 64#64) ↦₆₄ s1'.readReg64 (.gpr 26#5)) ∗
              ((s0.sp - 56#64) ↦₆₄ s1'.readReg64 (.gpr 25#5)) ∗
              ((s0.sp - 48#64) ↦₆₄ s1'.readReg64 (.gpr 24#5)) ∗
              ((s0.sp - 40#64) ↦₆₄ s1'.readReg64 (.gpr 23#5)) ∗
              ((s0.sp - 32#64) ↦₆₄ s1'.readReg64 (.gpr 22#5)) ∗
              ((s0.sp - 24#64) ↦₆₄ s1'.readReg64 (.gpr 21#5)) ∗
              ((s0.sp - 16#64) ↦₆₄ s1'.readReg64 (.gpr 20#5)) ∗
              ((s0.sp - 8#64) ↦₆₄ s1'.readReg64 (.gpr 19#5))) ∗
            vecHeader sret v0 v1 v2 ∗ (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev0) ∗ A.pool lb lk s0
        refine Entails.trans ?_
          (Entails.trans
            (sepConj_mono hrefold8320
              (sepConj_mono_left (Q := KeepN0) (Entails.trans hrefold4224 hcarve4224')))
            (by dsimp only [KeepN0]; sep_entail))
        dsimp only [KeepN0]; sep_entail
      · wp_conv_pre => simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        apply SepWP.exists_left; intro sc0
        wp_conv_pre => simp only [← sepConj_assoc]
        refine SepWP.weaken_pre (by sep_entail)
          (cliIoReadFile_nul_scan_loop pathBytes (idx := 0) (n := pathBytes.length)
            (pathPtr := pathPtr) (dst := s0.sp - 8320#64) (scratchPtr := s0.sp - 4224#64)
            (F := F_nul) (sc0 := sc0)
            h1_pos (Nat.zero_add _) hlt
            (by simp [arm64_norm])
            (by simpa [arm64_norm] using hrun1')
            (by simp only [State.spAligned, arm64_norm]; exact hsp0)
            (by simp [arm64_norm, hx0_1', bv_lin_norm])
            (by simp only [arm64_norm])
            (by simp [arm64_norm, bv_lin_norm])
            (by simp [arm64_norm])
            (fun sf_scan sc1 hpc_scan hpres_scan _ => ?_)
            (fun _ _ _ _ hno => False.elim (hno 0#8 hnul rfl)))
        dsimp only [F_nul]
        wp_conv_pre =>
          rw [show vecHeader sret v0 v1 v2 =
            (sret ↦₆₄ v0) ∗ ((sret + 8#64) ↦₆₄ v1) ∗ ((sret + 16#64) ↦₆₄ v2) from rfl]
          simp only [sepConj_assoc]
        have hx8_scan : sf_scan.readReg64 .x8 = sret :=
          hpres_scan.x8_eq.trans (by simp [arm64_norm, hx8_1'])
        have hrun_scan := hpres_scan.run_eq
        have hsp_scan := hpres_scan.spAligned_eq
        wp_sym_steps
        refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_scan)
          fun se hcpu_e0 hcl_e hnsp_e hsym_e => ?_
        have hcpu_e := hcpu_e0.1
        have ⟨hacp_0e, hpool_0e⟩ :=
          allocCallPreserved_of_seg hcpu1_0 hcpu_e0 hnsp_e hsym_e
            ((by simp [arm64_norm] : _ = sf_scan.tpidrEl0).trans
              (hpres_scan.tp_eq.trans (by simp [arm64_norm])))
            ((by simp [arm64_norm] : _ = sf_scan.sigActions).trans
              (hpres_scan.sig_eq.trans (by simp [arm64_norm])))
            ((by simp [arm64_norm] : _ = sf_scan.oracle).trans
              (hpres_scan.oracle_eq.trans (by simp [arm64_norm])))
        have hpool_eq : A.pool lb lk s0 = A.pool lb lk se := (A.pool_transport _ _ s0 se hpool_0e).symm
        have hsp_e_eq : se.sp = s0.sp - 8320#64 :=
          hcpu_e.sp_eq.trans ((by simp [arm64_norm] : _ = sf_scan.sp).trans
            (hpres_scan.sp_eq.trans (by simp [arm64_norm])))
        have hvregs_e : calleeSavedVRegs se = calleeSavedVRegs s0 :=
          hcpu_e.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sf_scan).trans
            (hpres_scan.vregs_eq.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs s1').trans hcpu1.calleeSavedVRegs)))
        refine SepWP.weaken_pre ?_
          (cliIoReadFile_ret_epilogue A hext3 (st0 := st0) (st1 := st1) (st2 := st2) (st3 := st3)
            (R_out := ((sret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (sret + 8#64) 16) ∗
              memcpySrc ro pathPtr pathBytes ∗ StdErrnoCell s0.tpidrEl0)
            (lb_f := lb) (lk_f := lk)
            hlo hhi hcl_e (hcpu_e.pc_eq.trans (by simp [arm64_norm]))
            (hcpu_e.status_eq.trans hrun_scan) hsp0 hsp_e_eq hvregs_e
            fun sf hpc_f hrun_f hsp_f hcs_f hcl_f hacp_ef _ hent =>
              herr_early (Or.inr hnul) sf hpc_f hrun_f hsp_f hcs_f hcl_f
                (allocCallPreserved_trans hacp_0e hacp_ef) hent)
        have hmerge4224 :
            ((s0.sp - 4224#64) ↦₈ sc1) ∗ memRegion (s0.sp - 4223#64) 4095 ⊢
              memRegion (s0.sp - 4224#64) 4096 := by
          simpa only [bv_lin_norm] using memRegion_byte_merge (s0.sp - 4224#64) sc1 4095 (by decide)
        have herr_sret :
            (sret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ ((sret + 8#64) ↦₆₄ v1) ∗ ((sret + 16#64) ↦₆₄ v2) ⊢
              (sret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (sret + 8#64) 16 :=
          vecHeader_to_err_sret sret v1 v2
        have hev_cell : (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev0) ⊢ StdErrnoCell s0.tpidrEl0 :=
          Entails.sepExists_right ev0 (Entails.refl _)
        rw [hpool_eq,
          hcpu1.readReg64 (.gpr 29#5), hcpu1.readReg64 (.gpr 30#5),
          hcpu1.readReg64 (.gpr 28#5), hcpu1.readReg64 (.gpr 27#5),
          hcpu1.readReg64 (.gpr 26#5), hcpu1.readReg64 (.gpr 25#5),
          hcpu1.readReg64 (.gpr 24#5), hcpu1.readReg64 (.gpr 23#5),
          hcpu1.readReg64 (.gpr 22#5), hcpu1.readReg64 (.gpr 21#5),
          hcpu1.readReg64 (.gpr 20#5), hcpu1.readReg64 (.gpr 19#5)]
        dsimp only [cliIoSavedRegs12]; simp only [bv_lin_norm]
        let KeepN1 : SepProp :=
          stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
            memRegion (s0.sp - 8320#64) 4096 ∗
            vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
            (((s0.sp - 96#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
              ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
              ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 28#5)) ∗
              ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (.gpr 27#5)) ∗
              ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗
              ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
              ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
              ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
              ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
              ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
              ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
              ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5))) ∗
            memcpySrc ro pathPtr pathBytes ∗ A.pool lb lk se
        refine Entails.trans ?_
          (Entails.trans (sepConj_mono hmerge4224 (sepConj_mono herr_sret (sepConj_mono_left (Q := KeepN1) hev_cell)))
            (by dsimp only [KeepN1]; sep_entail))
        dsimp only [KeepN1]; sep_entail
    · apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl0
        (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoOpenSym)
      intro s1' hcpu1_0; have hcpu1 := hcpu1_0.1
      change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
      have hpc1' : s1'.pc = cliIoPl03.base := hcpu1.pc_eq.trans hpc0
      have hrun1' : s1'.status = .Running := hcpu1.status_eq.trans hrun0
      have hsp1_in : s1'.sp = s0.sp := hcpu1.sp_eq
      have hsp1' : s1'.spAligned = true := by rw [hcpu1.spAligned]; exact hsp0
      have hx0_1' : s1'.readReg64 .x0 = pathPtr := (hcpu1.readReg64 .x0).trans hx0
      have hx1_1' : s1'.readReg64 .x1 = BitVec.ofNat 64 pathBytes.length := (hcpu1.readReg64 .x1).trans hx1_bv
      have hx8_1' : s1'.readReg64 .x8 = sret := (hcpu1.readReg64 .x8).trans hx8
      by_cases hnil : pathBytes = []
      · subst hnil
        have hnil_len : ([] : List (BitVec 8)).length = 0 := rfl
        rw [hnil_len] at hx1_1'
        apply rustSepWP_cut (mid := cliIoPl03.base + 112#64)
        wp_sym_steps
        refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun1') ?_
        have hcarve8320 :
            memRegion (s0.sp - 8320#64) 4096 =
              ((∃∗ z0 : BitVec 8, (s0.sp - 8320#64) ↦₈ z0) ∗ memRegion (s0.sp - 8319#64) 4095) := by
          simpa only [bv_lin_norm] using memRegion_succ_off (s0.sp - 8320#64) 0 4095 (by decide)
        let KeepEmpty0 : SepProp :=
          memcpySrc ro pathPtr [] ∗
            stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
            vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
            (((s0.sp - 96#64) ↦₆₄ s1'.readReg64 (.gpr 29#5)) ∗
              ((s0.sp - 88#64) ↦₆₄ s1'.readReg64 (.gpr 30#5)) ∗
              ((s0.sp - 80#64) ↦₆₄ s1'.readReg64 (.gpr 28#5)) ∗
              ((s0.sp - 72#64) ↦₆₄ s1'.readReg64 (.gpr 27#5)) ∗
              ((s0.sp - 64#64) ↦₆₄ s1'.readReg64 (.gpr 26#5)) ∗
              ((s0.sp - 56#64) ↦₆₄ s1'.readReg64 (.gpr 25#5)) ∗
              ((s0.sp - 48#64) ↦₆₄ s1'.readReg64 (.gpr 24#5)) ∗
              ((s0.sp - 40#64) ↦₆₄ s1'.readReg64 (.gpr 23#5)) ∗
              ((s0.sp - 32#64) ↦₆₄ s1'.readReg64 (.gpr 22#5)) ∗
              ((s0.sp - 24#64) ↦₆₄ s1'.readReg64 (.gpr 21#5)) ∗
              ((s0.sp - 16#64) ↦₆₄ s1'.readReg64 (.gpr 20#5)) ∗
              ((s0.sp - 8#64) ↦₆₄ s1'.readReg64 (.gpr 19#5))) ∗
            vecHeader sret v0 v1 v2 ∗ (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev0) ∗ A.pool lb lk s0
        refine SepWP.weaken_pre
          (P' := ((∃∗ z0 : BitVec 8, (s0.sp - 8320#64) ↦₈ z0) ∗ memRegion (s0.sp - 8319#64) 4095) ∗
            memRegion (s0.sp - 4224#64) 4096 ∗ KeepEmpty0)
          (by rw [← hcarve8320]
              refine Entails.trans ?_
                (Entails.trans (sepConj_mono hrefold8320 (sepConj_mono_left (Q := KeepEmpty0) hrefold4224))
                  (by dsimp only [KeepEmpty0]; sep_entail))
              dsimp only [KeepEmpty0]; sep_entail) ?_
        wp_conv_pre => dsimp only [KeepEmpty0]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        apply SepWP.exists_left; intro z0
        wp_sym_steps
        refine SepWP.done cliIoReadFile_open_pc (by simpa [arm64_norm] using hrun1')
          fun sm hcpu_m0 hcl_m hnsp_m hsym_m => ?_
        have hcpu_m := hcpu_m0.1
        have ⟨hacp_0m, hpool_0m⟩ :=
          allocCallPreserved_of_seg hcpu1_0 hcpu_m0 hnsp_m hsym_m
            (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        have hpool_eq : A.pool lb lk s0 = A.pool lb lk sm := (A.pool_transport _ _ s0 sm hpool_0m).symm
        have hsp_m_eq : sm.sp = s0.sp - 8320#64 := hcpu_m.sp_eq.trans (by simp [arm64_norm])
        have hsp_m : sm.spAligned = true := by
          simp only [State.spAligned]; rw [hsp_m_eq]; exact s0.spAligned_sub 8320#64 hsp0
        have hw1_m : sm.readReg32 .x1 = O_CLOEXEC_W32 := by
          rw [State.readReg32, hcpu_m.readReg64 .x1]; simp [arm64_norm, O_CLOEXEC_W32]
        refine SepWP.weaken_pre ?_
          (hat_open hlt hnul sm ev0 v0 v1 v2 st0 st1 st2 st3
            hcl_m (hcpu_m.pc_eq.trans cliIoReadFile_open_pc) (hcpu_m.status_eq.trans hrun1')
            hsp_m_eq hsp_m
            (by rw [hcpu_m.readReg64 .lr]; simp [arm64_norm])
            (by rw [hcpu_m.readReg64 .x0]; simp [arm64_norm])
            hw1_m
            (by rw [hcpu_m.readReg64]; simp [arm64_norm])
            (by rw [hcpu_m.readReg64]; simp [arm64_norm])
            (hcpu_m.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs s1').trans hcpu1.calleeSavedVRegs))
            hacp_0m)
        have hcstr_nil : cstrBytes (cPathOf []) = [0#8] := by rw [cstrBytes_cPathOf]; rfl
        rw [hcstr_nil, pointsToBytes_singleton, hpool_eq,
          hcpu1.readReg64 (.gpr 29#5), hcpu1.readReg64 (.gpr 30#5),
          hcpu1.readReg64 (.gpr 28#5), hcpu1.readReg64 (.gpr 27#5),
          hcpu1.readReg64 (.gpr 26#5), hcpu1.readReg64 (.gpr 25#5),
          hcpu1.readReg64 (.gpr 24#5), hcpu1.readReg64 (.gpr 23#5),
          hcpu1.readReg64 (.gpr 22#5), hcpu1.readReg64 (.gpr 21#5),
          hcpu1.readReg64 (.gpr 20#5), hcpu1.readReg64 (.gpr 19#5)]
        dsimp only [cliIoSavedRegs12]; simp only [bv_lin_norm]
        sep_entail
      · have h1_pos : 1 ≤ pathBytes.length := List.length_pos_iff.mpr hnil
        have hnez_len : (BitVec.ofNat 64 pathBytes.length == 0#64) = false :=
          bv64_beq_ofNat_false (b := 0) (by omega) (by omega) (by decide)
        apply rustSepWP_cut (mid := cliIoPl03.base + 84#64)
        wp_sym_steps
        refine SepWP.done (by simp [arm64_norm])
          (by simpa [arm64_norm] using hrun1') ?_
        let F_ok : SepProp :=
          memRegion (s0.sp - 4223#64) 4095 ∗
            stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
            vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
            cliIoSavedRegs12 s0 ∗
            vecHeader sret v0 v1 v2 ∗ (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev0) ∗ A.pool lb lk s0
        have hcarve4224' :
            memRegion (s0.sp - 4224#64) 4096 ⊢
              (∃∗ sc0 : BitVec 8, (s0.sp - 4224#64) ↦₈ sc0) ∗ memRegion (s0.sp - 4223#64) 4095 := by
          rw [show memRegion (s0.sp - 4224#64) 4096 =
            ((∃∗ sc0 : BitVec 8, (s0.sp - 4224#64) ↦₈ sc0) ∗ memRegion (s0.sp - 4223#64) 4095) by
              simpa only [bv_lin_norm] using memRegion_succ_off (s0.sp - 4224#64) 0 4095 (by decide)]
          exact Entails.refl _
        refine SepWP.weaken_pre
          (P' := memcpySrc ro (pathPtr + 0#64) pathBytes ∗
            memRegion ((s0.sp - 8320#64) + 0#64) 4096 ∗
            (∃∗ sc0 : BitVec 8, (s0.sp - 4224#64) ↦₈ sc0) ∗ F_ok) ?_ ?_
        · rw [hcpu1.readReg64 (.gpr 29#5), hcpu1.readReg64 (.gpr 30#5),
            hcpu1.readReg64 (.gpr 28#5), hcpu1.readReg64 (.gpr 27#5),
            hcpu1.readReg64 (.gpr 26#5), hcpu1.readReg64 (.gpr 25#5),
            hcpu1.readReg64 (.gpr 24#5), hcpu1.readReg64 (.gpr 23#5),
            hcpu1.readReg64 (.gpr 22#5), hcpu1.readReg64 (.gpr 21#5),
            hcpu1.readReg64 (.gpr 20#5), hcpu1.readReg64 (.gpr 19#5)]
          dsimp only [F_ok, cliIoSavedRegs12]; simp only [bv_lin_norm]
          let KeepOk0 : SepProp :=
            memcpySrc ro pathPtr pathBytes ∗
              stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
              vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
              (((s0.sp - 96#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
                ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
                ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 28#5)) ∗
                ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (.gpr 27#5)) ∗
                ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗
                ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
                ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
                ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
                ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
                ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
                ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
                ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5))) ∗
              vecHeader sret v0 v1 v2 ∗ (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev0) ∗ A.pool lb lk s0
          refine Entails.trans ?_
            (Entails.trans
              (sepConj_mono hrefold8320
                (sepConj_mono_left (Q := KeepOk0) (Entails.trans hrefold4224 hcarve4224')))
              (by dsimp only [KeepOk0]; simp only [bv_lin_norm]; sep_entail))
          dsimp only [KeepOk0]; simp only [bv_lin_norm]; sep_entail
        · wp_conv_pre => simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
          apply SepWP.exists_left; intro sc0
          wp_conv_pre => simp only [← sepConj_assoc]
          refine SepWP.weaken_pre (by sep_entail)
            (cliIoReadFile_nul_scan_loop pathBytes (idx := 0) (n := pathBytes.length)
              (pathPtr := pathPtr) (dst := s0.sp - 8320#64) (scratchPtr := s0.sp - 4224#64)
              (F := F_ok) (sc0 := sc0)
              h1_pos (Nat.zero_add _) hlt
              (by simp [arm64_norm])
              (by simpa [arm64_norm] using hrun1')
              (by simp only [State.spAligned, arm64_norm]; exact hsp0)
              (by simp [arm64_norm, hx0_1', bv_lin_norm])
              (by simp only [arm64_norm])
              (by simp [arm64_norm, bv_lin_norm])
              (by simp [arm64_norm])
              (fun _ _ _ _ hmem => False.elim (hnul hmem))
              (fun sf_scan sc1 hpc_scan hpres_scan _ => ?_))
          dsimp only [F_ok]
          wp_conv_pre =>
            rw [show 4096 - pathBytes.length = (4095 - pathBytes.length) + 1 by omega,
              memRegion_succ_off (s0.sp - 8320#64) pathBytes.length (4095 - pathBytes.length) (by omega)]
            simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
          apply SepWP.exists_left; intro z_nul
          have hx1_scan : sf_scan.readReg64 .x1 = BitVec.ofNat 64 pathBytes.length :=
            hpres_scan.x1_eq.trans (by simp [arm64_norm, hx1_1'])
          have hx8_scan : sf_scan.readReg64 .x8 = sret :=
            hpres_scan.x8_eq.trans (by simp [arm64_norm, hx8_1'])
          have hsp_scan_eq : sf_scan.sp = s0.sp - 8320#64 :=
            hpres_scan.sp_eq.trans (by simp [arm64_norm])
          have hrun_scan := hpres_scan.run_eq
          have hsp_scan := hpres_scan.spAligned_eq
          wp_sym_steps
          refine SepWP.done cliIoReadFile_open_pc (by simpa [arm64_norm] using hrun_scan)
            fun sm hcpu_m0 hcl_m hnsp_m hsym_m => ?_
          have hcpu_m := hcpu_m0.1
          have ⟨hacp_0m, hpool_0m⟩ :=
            allocCallPreserved_of_seg hcpu1_0 hcpu_m0 hnsp_m hsym_m
              ((by simp [arm64_norm] : _ = sf_scan.tpidrEl0).trans
                (hpres_scan.tp_eq.trans (by simp [arm64_norm])))
              ((by simp [arm64_norm] : _ = sf_scan.sigActions).trans
                (hpres_scan.sig_eq.trans (by simp [arm64_norm])))
              ((by simp [arm64_norm] : _ = sf_scan.oracle).trans
                (hpres_scan.oracle_eq.trans (by simp [arm64_norm])))
          have hpool_eq : A.pool lb lk s0 = A.pool lb lk sm := (A.pool_transport _ _ s0 sm hpool_0m).symm
          have hsp_m_eq : sm.sp = s0.sp - 8320#64 :=
            hcpu_m.sp_eq.trans (by simp [arm64_norm, hsp_scan_eq])
          have hsp_m : sm.spAligned = true := by
            simp only [State.spAligned]; rw [hsp_m_eq]; exact s0.spAligned_sub 8320#64 hsp0
          have hw1_m : sm.readReg32 .x1 = O_CLOEXEC_W32 := by
            rw [State.readReg32, hcpu_m.readReg64 .x1]; simp [arm64_norm, O_CLOEXEC_W32]
          have hx29_m : sm.readReg64 (.gpr 29#5) = s0.sp - 96#64 := by
            rw [hcpu_m.readReg64 (.gpr 29#5)]; simp only [arm64_norm]
            exact hpres_scan.x29_eq.trans (by simp [arm64_norm])
          have hvregs_m : calleeSavedVRegs sm = calleeSavedVRegs s0 :=
            hcpu_m.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sf_scan).trans
              (hpres_scan.vregs_eq.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs s1').trans hcpu1.calleeSavedVRegs)))
          refine SepWP.weaken_pre ?_
            (hat_open hlt hnul sm ev0 v0 v1 v2 st0 st1 st2 st3
              hcl_m (hcpu_m.pc_eq.trans cliIoReadFile_open_pc) (hcpu_m.status_eq.trans hrun_scan)
              hsp_m_eq hsp_m
              (by rw [hcpu_m.readReg64 .lr]; simp [arm64_norm])
              (by rw [hcpu_m.readReg64 .x0]; simp [arm64_norm])
              hw1_m
              (by rw [hcpu_m.readReg64]; simp [arm64_norm])
              hx29_m hvregs_m hacp_0m)
          have hmerge4224 :
              ((s0.sp - 4224#64) ↦₈ sc1) ∗ memRegion (s0.sp - 4223#64) 4095 ⊢
                memRegion (s0.sp - 4224#64) 4096 := by
            simpa only [bv_lin_norm] using memRegion_byte_merge (s0.sp - 4224#64) sc1 4095 (by decide)
          have hcstr_eq :
              ((s0.sp - 8320#64) ↦ₛ pathBytes) ∗
                (((s0.sp - 8320#64) + BitVec.ofNat 64 pathBytes.length) ↦₈ 0#8) =
              ((s0.sp - 8320#64) ↦ₛ cstrBytes (cPathOf pathBytes)) := by
            rw [cstrBytes_cPathOf, pointsToBytes_snoc]
          rw [hpool_eq]
          let KeepOk1 : SepProp :=
            stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗
              ((s0.sp - 8320#64) ↦ₛ cstrBytes (cPathOf pathBytes)) ∗
              memRegion ((s0.sp - 8320#64) + BitVec.ofNat 64 (pathBytes.length + 1))
                (4095 - pathBytes.length) ∗
              vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
              cliIoSavedRegs12 s0 ∗
              memcpySrc ro pathPtr pathBytes ∗
              vecHeader sret v0 v1 v2 ∗ (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev0) ∗ A.pool lb lk sm
          refine Entails.trans ?_
            (Entails.trans (sepConj_mono_left (Q := KeepOk1) hmerge4224)
              (by dsimp only [KeepOk1]; simp only [bv_lin_norm]; sep_entail))
          dsimp only [KeepOk1]
          rw [← hcstr_eq]
          simp only [bv_lin_norm]
          sep_entail

end

end LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileOpenSteps
