/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSitesPlaced
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Call-Site Helpers and `SepWPp` Combinators for `main`

Relocatable `[LibsignalPlacement]` counterparts of `CallSites.lean` on Block `617` (`mProgPlaced H`),
parameterized over `[LsCodeInv CodeOk]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit

/-! ## Block-`617` Callee Corollaries (`withLsRoCl lsmpl`) -/

theorem main_panic_handle_error_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {uuidParse : UuidParser} {hookStack resStack : Nat}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack) :
    ((blkPC_617).rebase (blkPl_617).base H).externAt? (lsρ lsHandleErrorSymMain) =
      some Rust.panicked :=
  hc.handleErrorPanic

theorem main_shim_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A H) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsRustNoAllocShimSymCli)
      (withLsRoCl lsmpl session2ShimSpecX) :=
  hC.shim2_rocl (prog := lsProg_617 H) (i := 617)

theorem main_alloc_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A H) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsRustAllocSymCli)
      (withLsRoCl lsmpl (rustAllocSpecWithStack A extHookStack)) :=
  hC.alloc_rocl (prog := lsProg_617 H) (i := 617)

theorem main_dealloc_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A H) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsRustDeallocSymCli)
      (withLsRoCl lsmpl (rustDeallocExternSpecWithStack A extHookStack)) :=
  hC.dealloc_rocl (prog := lsProg_617 H) (i := 617)

theorem main_memcpy_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A H) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ memcpyName)
      (withLsRoCl lsmpl
        (CryptoVerification.LibsignalTripleRatchet.sessionMemcpySpec extHookStack)) :=
  hC.session_memcpy_rocl (prog := lsProg_617 H) (i := 617) extHookStack (Nat.le_refl _) (by decide)

theorem main_shim_fs_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : AllocContractsFsPlaced A H) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsRustNoAllocShimSymCli)
      (withLsRoCl lsmpl session2ShimSpecX.keepsFs) :=
  hC.shim2_rocl (prog := lsProg_617 H) (i := 617)

theorem main_alloc_fs_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : AllocContractsFsPlaced A H) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsRustAllocSymCli)
      (withLsRoCl lsmpl (rustAllocSpecWithStack A extHookStack).keepsFs) :=
  hC.alloc_rocl (prog := lsProg_617 H) (i := 617)

theorem main_dealloc_fs_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : AllocContractsFsPlaced A H) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsRustDeallocSymCli)
      (withLsRoCl lsmpl (rustDeallocExternSpecWithStack A extHookStack).keepsFs) :=
  hC.dealloc_rocl (prog := lsProg_617 H) (i := 617)

theorem main_memcpy_fs_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : AllocContractsFsPlaced A H) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ memcpyName)
      (withLsRoCl lsmpl
        (CryptoVerification.LibsignalTripleRatchet.sessionMemcpySpec extHookStack).keepsFs) :=
  hC.session_memcpy_rocl (prog := lsProg_617 H) (i := 617) extHookStack (Nat.le_refl _) (by decide)

theorem main_memcpy2_fs_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : AllocContractsFsPlaced A H) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ memcpyName)
      (withLsRoCl lsmpl session2MemcpySpecX.keepsFs) :=
  hC.memcpy2_rocl (prog := lsProg_617 H) (i := 617)

theorem main_libc_memcpy_fs_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : AllocContractsFsPlaced A H) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ memcpyName)
      (withLsRoCl lsmpl (libcMemcpySpec extHookStack).keepsFs) :=
  hC.memcpy_rocl (prog := lsProg_617 H) (i := 617) extHookStack (Nat.le_refl _) (by decide)

theorem main_session_memcpy_ro_fs_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : AllocContractsFsPlaced A H) (stk : Nat) (hstk : extHookStack ≤ stk) (h64 : stk ≤ 2 ^ 64) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ memcpyName)
      (withLsRoCl lsmpl
        (withStack CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec stk).keepsFs) :=
  hC.session_memcpy_region_ro_rocl (prog := lsProg_617 H) (i := 617) stk hstk h64

theorem main_strlen_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {uuidParse : UuidParser} {hookStack resStack : Nat}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ "strlen")
      (withLsRoCl lsmpl (strlenSpec hookStack)) :=
  hc.strlen

theorem main_fromUtf8_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {uuidParse : UuidParser} {hookStack resStack : Nat}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ lsFromUtf8Sym)
      (withLsRoCl lsmpl (fromUtf8AsciiSpec hookStack)) :=
  hc.fromUtf8

theorem main_address_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {uuidParse : UuidParser} {hookStack resStack : Nat}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsmpl.base 580)
      (withLsRoCl lsmpl (addressSpec A uuidParse resStack)) :=
  hc.address

theorem main_reserve16_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {uuidParse : UuidParser} {hookStack resStack : Nat}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsmpl.base 561)
      (withLsRoCl lsmpl (reserve16Spec A resStack)) :=
  hc.reserve16

theorem main_reserve1_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {uuidParse : UuidParser} {hookStack resStack : Nat}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsmpl.base 561)
      (withLsRoCl lsmpl (CryptoVerification.SpqrV1.Varint.doReserveSpecOf resStack A).keepsFs) :=
  hc.reserve1

theorem main_tryAllocateIn3_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {uuidParse : UuidParser} {hookStack resStack : Nat}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsmpl.base 588)
      (withLsRoCl lsmpl (tryAllocateInSpecOf resStack A).keepsFs) :=
  hc.tryAllocateIn3

/-! ## `SepWPp` Cut and Call Combinators -/

theorem sepWPp_seq_codeOk [LibsignalPlacement] {CodeOk : Memory → Prop} [hCI : LsCodeInv CodeOk]
    {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : CodeOk s.mem)
    (h : SepWP prog mid s P (fun sm Pm => CodeOk sm.mem → SepWPp prog ret sm Pm Q Qp oom) oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hcont⟩ | hoom⟩
  · obtain ⟨sf, hsteps', hout⟩ :=
      hcont (hCI.of_keepsFrozen hinv hsteps.keepsFrozen) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

set_option linter.unusedVariables false in
theorem main_call_rocl_steps [LibsignalPlacement] {CodeOk : Memory → Prop} [hCI : LsCodeInv CodeOk]
    {α : Type} {prog : Program}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (x : α)
    (hcall : subroutine_ok prog entry (withLsRoCl lsmpl spec))
    (hinv : CodeOk s.mem)
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hP : P ⊢ spec.pre x s ∗ F)
    (hpanic : ∀ sf R', sf.status = .Panicked →
      (sf.mem ⊨ spec.onPanic x s sf ∗ R') → Qp sf (spec.onPanic x s sf ∗ F) := by
      intro _ _ _ hp; exact (not_satisfies_false_sepConj hp).elim)
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False := by
      intro _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      intro _ _ _ ho; exact (not_satisfies_false_sepConj ho).elim)
    (hnext : ∀ sf : State,
      Steps prog s sf →
      CodeOk sf.mem →
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s.sp →
      CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp oom)
    (s0 : State := by exact s) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  have hm_pre : s.mem ⊨ (spec.pre x s ∗ F) ∗ R :=
    Satisfies.mono (sepConj_mono_left hP) hm
  have hpre : s.mem ⊨ (withLsRoCl lsmpl spec).pre x s ∗ (F ∗ R) := by
    dsimp only [withLsRoCl]
    rw [sepConj_comm (spec.pre x s), sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hCI.toRoCl hinv, by simpa only [sepConj_assoc] using hm_pre⟩
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hpre hsp hL
  rcases hout with
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ |
      ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_s, hpost⟩
  · dsimp only [withLsRoCl] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨_, hpost⟩
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps (hCI.of_keepsFrozen hinv hsteps.keepsFrozen) hpcm hrunm hspm hcsm
        R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withLsRoCl] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, spec.onPanic x s sm ∗ F,
      by simpa only [sepConj_assoc] using hpost,
      hpanic sm (F ∗ R) hpan hpost⟩)⟩
  · exact (hexit sm code (F ∗ R) hex hpost).elim
  · dsimp only [withLsRoCl] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom_s, hoom sm R hoom_s hpost⟩)⟩

set_option linter.unusedVariables false in
theorem main_call_rocl [LibsignalPlacement] {CodeOk : Memory → Prop} [hCI : LsCodeInv CodeOk]
    {α : Type} {prog : Program}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (x : α)
    (hcall : subroutine_ok prog entry (withLsRoCl lsmpl spec))
    (hinv : CodeOk s.mem)
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hP : P ⊢ spec.pre x s ∗ F)
    (hpanic : ∀ sf R', sf.status = .Panicked →
      (sf.mem ⊨ spec.onPanic x s sf ∗ R') → Qp sf (spec.onPanic x s sf ∗ F) := by
      intro _ _ _ hp; exact (not_satisfies_false_sepConj hp).elim)
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False := by
      intro _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      intro _ _ _ ho; exact (not_satisfies_false_sepConj ho).elim)
    (hnext : ∀ sf : State,
      CodeOk sf.mem →
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s.sp →
      CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp oom)
    (s0 : State := by exact s) :
    SepWPp prog ret s P Q Qp oom :=
  main_call_rocl_steps x hcall hinv hpc hrun hsp hlr hP hpanic hexit hoom
    (fun sf _ => hnext sf) s0

set_option linter.unusedVariables false in
theorem main_call_plain_steps [LibsignalPlacement] {CodeOk : Memory → Prop} [hCI : LsCodeInv CodeOk]
    {α : Type} {prog : Program}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (x : α)
    (hcall : subroutine_ok prog entry spec)
    (hinv : CodeOk s.mem)
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hP : P ⊢ spec.pre x s ∗ F)
    (hpanic : ∀ sf R', sf.status = .Panicked →
      (sf.mem ⊨ spec.onPanic x s sf ∗ R') → Qp sf (spec.onPanic x s sf ∗ F) := by
      intro _ _ _ hp; exact (not_satisfies_false_sepConj hp).elim)
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False := by
      intro _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      intro _ _ _ ho; exact (not_satisfies_false_sepConj ho).elim)
    (hnext : ∀ sf : State,
      Steps prog s sf →
      CodeOk sf.mem →
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s.sp →
      CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp oom)
    (s0 : State := by exact s) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  have hm_pre : s.mem ⊨ (spec.pre x s ∗ F) ∗ R :=
    Satisfies.mono (sepConj_mono_left hP) hm
  have hpre : s.mem ⊨ spec.pre x s ∗ (F ∗ R) := by
    simpa only [sepConj_assoc] using hm_pre
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hpre hsp hL
  rcases hout with
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ |
      ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_s, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps (hCI.of_keepsFrozen hinv hsteps.keepsFrozen) hpcm hrunm hspm hcsm
        R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, spec.onPanic x s sm ∗ F,
      by simpa only [sepConj_assoc] using hpost,
      hpanic sm (F ∗ R) hpan hpost⟩)⟩
  · exact (hexit sm code (F ∗ R) hex hpost).elim
  · exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom_s, hoom sm R hoom_s hpost⟩)⟩

set_option linter.unusedVariables false in
theorem main_call_plain [LibsignalPlacement] {CodeOk : Memory → Prop} [hCI : LsCodeInv CodeOk]
    {α : Type} {prog : Program}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {s : State}
    {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (x : α)
    (hcall : subroutine_ok prog entry spec)
    (hinv : CodeOk s.mem)
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hP : P ⊢ spec.pre x s ∗ F)
    (hpanic : ∀ sf R', sf.status = .Panicked →
      (sf.mem ⊨ spec.onPanic x s sf ∗ R') → Qp sf (spec.onPanic x s sf ∗ F) := by
      intro _ _ _ hp; exact (not_satisfies_false_sepConj hp).elim)
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False := by
      intro _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      intro _ _ _ ho; exact (not_satisfies_false_sepConj ho).elim)
    (hnext : ∀ sf : State,
      CodeOk sf.mem →
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s.sp →
      CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp oom)
    (s0 : State := by exact s) :
    SepWPp prog ret s P Q Qp oom :=
  main_call_plain_steps x hcall hinv hpc hrun hsp hlr hP hpanic hexit hoom
    (fun sf _ => hnext sf) s0

end CryptoVerification.SignalSession.Cli.MainHops
