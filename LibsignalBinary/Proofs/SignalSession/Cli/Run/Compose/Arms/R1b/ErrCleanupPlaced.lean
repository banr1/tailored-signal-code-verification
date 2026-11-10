/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CommonPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanup
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSites
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq

/-!
# Relocatable OOM Stubs and Error Cleanup Chain for Arm `R1b`

Relocatable (`[LibsignalPlacement]`) error-context structure and cleanup continuation helpers for
Arm `R1b` on Block `579`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open Arm64.Process
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.Run.Placed

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local simp, local arm64_norm, local wp_norm] runPcPlaced_eq BitVec.ofNat_eq_ofNat

theorem r1b_oom_2d44_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {g : RunCall} {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H)
    (hst : InRunPlaced r1b_CodeOk s0 s 0x2d44) (hpanic : PanicK g s0 Qp)
    (hfail : allocFailedIn s0 s) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s P Q Qp (runOom s0) := by
  have hpc := hst.pc; have hrun := hst.run; have hinv := hst.inv
  change s.pc = (blkPl_579).base + 0x2d44#64 at hpc
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro
    (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") hinv
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state_placed fun sm hsm _ => ?_
  exact r1b_handle_error_panic_placed hh
    (by simp only [hsm, arm64_norm])
    (by simp only [hsm, arm64_norm, hrun]) hpanic
    (r1b_allocFailedIn_mono hfail (by simp only [hsm, arm64_norm, List.prefix_rfl]))

theorem r1b_oom_2d68_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {g : RunCall} {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H)
    (hst : InRunPlaced r1b_CodeOk s0 s 0x2d68) (hpanic : PanicK g s0 Qp)
    (hfail : allocFailedIn s0 s) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s P Q Qp (runOom s0) := by
  have hpc := hst.pc; have hrun := hst.run; have hinv := hst.inv
  change s.pc = (blkPl_579).base + 0x2d68#64 at hpc
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro
    (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") hinv
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state_placed fun sm hsm _ => ?_
  exact r1b_handle_error_panic_placed hh
    (by simp only [hsm, arm64_norm])
    (by simp only [hsm, arm64_norm, hrun]) hpanic
    (r1b_allocFailedIn_mono hfail (by simp only [hsm, arm64_norm, List.prefix_rfl]))

theorem r1b_oom_2d5c_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {g : RunCall} {s0 s : State} {v0 v1 : BitVec 64} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H)
    (hst : InRunPlaced r1b_CodeOk s0 s 0x2d5c) (hpanic : PanicK g s0 Qp)
    (hfail : allocFailedIn s0 s) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (((fsp + 0x4e0#64) ↦₆₄ v1) ∗ ((fsp + 0x120#64) ↦₆₄ v0) ∗ F) Q Qp (runOom s0) := by
  intro fsp
  have hpc := hst.pc; have hrun := hst.run
  have hsp : s.sp = fsp := hst.sp
  have hinv := hst.inv; have hsp0 := hst.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hsp0
  change s.pc = (blkPl_579).base + 0x2d5c#64 at hpc
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro
    (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") hinv
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state_placed fun sm hsm _ => ?_
  exact r1b_handle_error_panic_placed hh
    (by simp only [hsm, arm64_norm])
    (by simp only [hsm, arm64_norm, hrun]) hpanic
    (r1b_allocFailedIn_mono hfail (by simp only [hsm, arm64_norm, List.prefix_rfl]))

theorem r1b_oom_2d74_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {g : RunCall} {s0 s : State} {v0 v1 : BitVec 64} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H)
    (hst : InRunPlaced r1b_CodeOk s0 s 0x2d74) (hpanic : PanicK g s0 Qp)
    (hfail : allocFailedIn s0 s) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (((fsp + 0x4e0#64) ↦₆₄ v1) ∗ ((fsp + 0x158#64) ↦₆₄ v0) ∗ F) Q Qp (runOom s0) := by
  intro fsp
  have hpc := hst.pc; have hrun := hst.run
  have hsp : s.sp = fsp := hst.sp
  have hinv := hst.inv; have hsp0 := hst.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hsp0
  change s.pc = (blkPl_579).base + 0x2d74#64 at hpc
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro
    (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") hinv
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state_placed fun sm hsm _ => ?_
  exact r1b_handle_error_panic_placed hh
    (by simp only [hsm, arm64_norm])
    (by simp only [hsm, arm64_norm, hrun]) hpanic
    (r1b_allocFailedIn_mono hfail (by simp only [hsm, arm64_norm, List.prefix_rfl]))

structure r1b_ErrCtxPlaced [LibsignalPlacement] (CodeOk : Memory → Prop)
    (g : RunCall) (d : Init1Data) (s0 s : State) (off : Nat) : Prop where
  st : InRunPlaced CodeOk s0 s off
  x19 : s.readReg64 (.gpr 19#5) = g.stores
  x20 : s.readReg64 (.gpr 20#5) = g.res
  x21 : s.readReg64 (.gpr 21#5) = d.meG.name.cap
  trace : s0.trace <+: s.trace
  hist : RunHistOk g.i s0 s
  ans : g.a = some none

theorem r1b_ErrCtxPlaced.of_call [LibsignalPlacement] {CodeOk : Memory → Prop}
    {g : RunCall} {d : Init1Data} {s0 st_bl sf : State} {off off' : Nat}
    (hc : r1b_ErrCtxPlaced CodeOk g d s0 st_bl off)
    (hin : InRunPlaced CodeOk s0 sf off')
    (hcs : CalleeSavedPreserved st_bl sf)
    (hfs : sf.fs.files = st_bl.fs.files)
    (htr : sf.trace = st_bl.trace) :
    r1b_ErrCtxPlaced CodeOk g d s0 sf off' := {
  st := hin
  x19 := hcs.1.trans hc.x19
  x20 := hcs.2.1.trans hc.x20
  x21 := hcs.2.2.1.trans hc.x21
  trace := htr ▸ hc.trace
  hist := ⟨hfs.trans hc.hist.1, htr ▸ hc.hist.2⟩
  ans := hc.ans
}

private theorem r1b_addrNameHeap_to_ownedBytes_placed (A : RustAlloc) (g : AddrGhost) :
    addrNameHeap A g ⊢
      ownedBytes A g.name.cap g.name.ptr (BitVec.ofNat 64 g.name.bytes.length) g.name.bytes := by
  dsimp only [addrNameHeap, ownedBytes]
  apply Entails.pure_left
  rintro ⟨hle, hlt, hne⟩
  refine Entails.pure_right ⟨by simp, hle, hlt, hne⟩ (Entails.refl _)

private theorem r1b_cleanup_2c68_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hbnd : r1b_StackBounds B resStack)
    (hst : InRunPlaced r1b_CodeOk s0 s 0x2c68)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (htrace : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (hpanic : PanicK g s0 Qp) (hrej : RejectKPlaced r1b_CodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
        storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        runSaved s0 ∗ r1b_errFrameRest (runFsp s0) ∗
        memRegion ((runFsp s0) + 0x110#64) 8 ∗ memRegion ((runFsp s0) + 0x11c#64) 4 ∗
        memRegion ((runFsp s0) + 0x120#64) 16 ∗ memRegion ((runFsp s0) + 0x150#64) 16 ∗
        memRegion ((runFsp s0) + 0x168#64) 24 ∗ memRegion ((runFsp s0) + 0x188#64) 48 ∗
        memRegion ((runFsp s0) + 0x1b8#64) 24 ∗
        protocolAddressAt A d.peerG (fsp + 0x2a0#64) ∗
        memRegion (fsp + 0x4d0#64) 48 ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap)
      Q Qp (runOom s0) := by
  intro fsp
  have haddr : protocolAddressAt A d.peerG (fsp + 0x2a0#64) =
      ((fsp + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((fsp + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
        addrUpperAt (fsp + 0x2b0#64) d.peerG ∗ addrNameHeap A d.peerG := by
    rw [protocolAddressAt_eq_parts A d.peerG (fsp + 0x2a0#64)]
    have h2a8 : fsp + 0x2a0#64 + 8#64 = fsp + 0x2a8#64 := by bv_omega
    have h2b0 : fsp + 0x2a0#64 + 16#64 = fsp + 0x2b0#64 := by bv_omega
    rw [h2a8, h2b0]
  have hpeer32 : ∀ capv ptrv : BitVec 64,
      ((fsp + 0x2a0#64) ↦₆₄ capv) ∗ ((fsp + 0x2a8#64) ↦₆₄ ptrv) ∗
        addrUpperAt (fsp + 0x2b0#64) d.peerG ⊢ memRegion (fsp + 0x2a0#64) 32 := by
    intro capv ptrv
    have hup := addrUpperAt_entails_memRegion (fsp + 0x2b0#64) d.peerG
    have h2a8 : fsp + 0x2b0#64 = (fsp + 0x2a8#64) + 8#64 := by bv_omega
    have h2a0 : fsp + 0x2a8#64 = (fsp + 0x2a0#64) + 8#64 := by bv_omega
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right hup)) ?_
    refine Entails.trans (sepConj_mono_right (by rw [h2a8]; exact r1b_cell64_cons ptrv (by decide))) ?_
    rw [h2a0]; exact r1b_cell64_cons capv (by decide)
  rw [haddr]
  have hpc := hst.pc; have hrun := hst.run
  have hsp : s.sp = fsp := hst.sp
  have hfp := hst.fp; have hinv := hst.inv; have hvregs := hst.vregs; have hsp0 := hst.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hsp0
  change s.pc = (blkPl_579).base + 0x2c68#64 at hpc
  by_cases hcap : d.peerG.name.cap = 0#64
  · rw [hcap]
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x2c7c) hinv
    rw [runPcPlaced_eq]
    (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
    have hst_m : InRunPlaced r1b_CodeOk s0 sm 0x2c7c := {
      pc := by simp [hsm, arm64_norm]
      run := by simp [hsm, arm64_norm, hrun]
      sp := by simpa [hsm, arm64_norm] using hst.sp
      fp := by simpa [hsm, arm64_norm] using hfp
      inv := hinv_m
      vregs := by simpa [calleeSavedVRegs, hsm, arm64_norm] using hvregs
      spAligned := hsp0
    }
    have hrej_m : AtRejectPlaced r1b_CodeOk g StoresGhost.opened .postDispatch s0 sm := {
      base := hst_m
      x19 := by simpa [hsm, arm64_norm] using hx19
      preRegs := fun h => by cases h
      trace := by simpa [hsm, arm64_norm] using htrace
      hist := ⟨by simpa [hsm, arm64_norm] using hhist.1,
        by simpa [hsm, arm64_norm] using hhist.2⟩
      ans := hans
    }
    refine MainHops.sepWPp_weaken_pre ?_ (hrej sm StoresGhost.opened .postDispatch hrej_m)
    dsimp only [rejectMem]
    have h1 := hpeer32 0#64 d.peerG.name.ptr
    have h2 : addrNameHeap A d.peerG ∗ anyHeap ⊢ anyHeap := entails_anyHeap _
    dsimp only [fsp] at h1 ⊢
    refine Entails.trans (Entails.of_eq (show _ =
      (runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56) ∗
      storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      runSaved s0 ∗
      (r1b_errFrameRest (runFsp s0) ∗ memRegion (runFsp s0 + 0x110#64) 8 ∗ memRegion (runFsp s0 + 0x11c#64) 4 ∗
        memRegion (runFsp s0 + 0x120#64) 16 ∗ memRegion (runFsp s0 + 0x150#64) 16 ∗
        memRegion (runFsp s0 + 0x168#64) 24 ∗ memRegion (runFsp s0 + 0x188#64) 48 ∗
        memRegion (runFsp s0 + 0x1b8#64) 24 ∗
        (((runFsp s0 + 0x2a0#64) ↦₆₄ 0#64) ∗ ((runFsp s0 + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          addrUpperAt (runFsp s0 + 0x2b0#64) d.peerG) ∗
        memRegion (runFsp s0 + 0x4d0#64) 48) ∗
      stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗
      (addrNameHeap A d.peerG ∗ anyHeap) by ac_rfl)) ?_
    refine sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono ?_
        (sepConj_mono_right (sepConj_mono_right h2))))))
    refine Entails.trans ?_ (r1b_rejoin_errFrame (runFsp s0))
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left h1))))))))
  · have hcap_f : (d.peerG.name.cap == 0#64) = false := beq_false_of_ne hcap
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := lsρ lsRustDeallocSymCli) hinv
    (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hsm_sp : sm.sp = runFsp s0 := by simpa only [hsm, arm64_norm] using hst.sp
    have hsm_fp : sm.readReg64 .fp = s0.sp - 0x60#64 := by simpa only [hsm, arm64_norm] using hfp
    have hsm_vr : calleeSavedVRegs sm = calleeSavedVRegs s0 := by
      simpa only [calleeSavedVRegs, hsm, arm64_norm] using hvregs
    have hsm_pc : sm.pc = lsρ lsRustDeallocSymCli := by
      simp only [hsm, arm64_norm]
    have hsm_lr : sm.readReg64 .lr = runPcPlaced 0x2c7c := by
      simp only [hsm, arm64_norm]
    dsimp only [fsp]
    apply MainHops.sepWPp_weaken_pre
    · refine Entails.trans (Entails.of_eq (show _ =
        addrNameHeap A d.peerG ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗
        (runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
          storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          runSaved s0 ∗ r1b_errFrameRest (runFsp s0) ∗
          memRegion (runFsp s0 + 0x110#64) 8 ∗ memRegion (runFsp s0 + 0x11c#64) 4 ∗
          memRegion (runFsp s0 + 0x120#64) 16 ∗ memRegion (runFsp s0 + 0x150#64) 16 ∗
          memRegion (runFsp s0 + 0x168#64) 24 ∗ memRegion (runFsp s0 + 0x188#64) 48 ∗
          memRegion (runFsp s0 + 0x1b8#64) 24 ∗
          (((runFsp s0 + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗
            ((runFsp s0 + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
            addrUpperAt (runFsp s0 + 0x2b0#64) d.peerG) ∗
          memRegion (runFsp s0 + 0x4d0#64) 48 ∗ anyHeap) by ac_rfl))
        (sepConj_mono_left (r1b_addrNameHeap_to_ownedBytes_placed A d.peerG))
    refine r1b_call_dealloc_ownedBytes_placed (Q := Q) (cap := d.peerG.name.cap) (ptr := d.peerG.name.ptr)
      (len := BitVec.ofNat 64 d.peerG.name.bytes.length) (bs := d.peerG.name.bytes)
      hh hbnd hinv_m hsm_pc (by simp only [hsm, arm64_norm, hrun])
      hsm_sp hsm_fp hsm_vr hsp0 hsm_lr
      (by simp only [hsm, arm64_norm]) (by simp only [hsm, arm64_norm]) (by simp only [hsm, arm64_norm])
      hcap hpanic ?_
    intro sf hin_f hcs_f hfs_f htr_f
    have hrej_f : AtRejectPlaced r1b_CodeOk g StoresGhost.opened .postDispatch s0 sf := {
      base := hin_f
      x19 := hcs_f.1.trans (by simpa [hsm, arm64_norm] using hx19)
      preRegs := fun h => by cases h
      trace := htr_f ▸ (by simpa [hsm, arm64_norm] using htrace)
      hist := ⟨by rw [hfs_f]; simpa [hsm, arm64_norm] using hhist.1,
        by rw [htr_f]; simpa [hsm, arm64_norm] using hhist.2⟩
      ans := hans
    }
    refine MainHops.sepWPp_weaken_pre ?_ (hrej sf StoresGhost.opened .postDispatch hrej_f)
    dsimp only [rejectMem]
    have h1 := hpeer32 d.peerG.name.cap d.peerG.name.ptr
    dsimp only [fsp] at h1 ⊢
    refine Entails.trans (Entails.of_eq (show _ =
      (runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56) ∗
      storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      runSaved s0 ∗
      (r1b_errFrameRest (runFsp s0) ∗ memRegion (runFsp s0 + 0x110#64) 8 ∗ memRegion (runFsp s0 + 0x11c#64) 4 ∗
        memRegion (runFsp s0 + 0x120#64) 16 ∗ memRegion (runFsp s0 + 0x150#64) 16 ∗
        memRegion (runFsp s0 + 0x168#64) 24 ∗ memRegion (runFsp s0 + 0x188#64) 48 ∗
        memRegion (runFsp s0 + 0x1b8#64) 24 ∗
        (((runFsp s0 + 0x2a0#64) ↦₆₄ d.peerG.name.cap) ∗ ((runFsp s0 + 0x2a8#64) ↦₆₄ d.peerG.name.ptr) ∗
          addrUpperAt (runFsp s0 + 0x2b0#64) d.peerG) ∗
        memRegion (runFsp s0 + 0x4d0#64) 48) ∗
      stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap by ac_rfl)) ?_
    refine sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left ?_))))
    refine Entails.trans ?_ (r1b_rejoin_errFrame (runFsp s0))
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left h1))))))))

private theorem r1b_cleanup_2c54_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hbnd : r1b_StackBounds B resStack)
    (hst : InRunPlaced r1b_CodeOk s0 s 0x2c54)
    (hx19 : s.readReg64 (.gpr 19#5) = g.stores)
    (hx22 : s.readReg64 (.gpr 22#5) = d.dirPtr)
    (hx24 : s.readReg64 (.gpr 24#5) = d.dirCap)
    (htrace : s0.trace <+: s.trace)
    (hhist : RunHistOk g.i s0 s)
    (hans : g.a = some none)
    (hpanic : PanicK g s0 Qp) (hrej : RejectKPlaced r1b_CodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
        storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
        runSaved s0 ∗ r1b_errFrameRest fsp ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 24 ∗ memRegion (fsp + 0x188#64) 48 ∗
        memRegion (fsp + 0x1b8#64) 24 ∗
        protocolAddressAt A d.peerG (fsp + 0x2a0#64) ∗
        memRegion (fsp + 0x4d0#64) 48 ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap)
      Q Qp (runOom s0) := by
  intro fsp
  have hpc := hst.pc; have hrun := hst.run
  have hfp := hst.fp; have hinv := hst.inv; have hvregs := hst.vregs; have hsp0 := hst.spAligned
  change s.pc = (blkPl_579).base + 0x2c54#64 at hpc
  by_cases hcap : d.dirCap = 0#64
  · rw [hcap] at hx24 ⊢
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x2c68) hinv
    rw [runPcPlaced_eq]
    (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
    have hst_m : InRunPlaced r1b_CodeOk s0 sm 0x2c68 := {
      pc := by simp [hsm, arm64_norm]
      run := by simp [hsm, arm64_norm, hrun]
      sp := by simpa [hsm, arm64_norm] using hst.sp
      fp := by simpa [hsm, arm64_norm] using hfp
      inv := hinv_m
      vregs := by simpa [calleeSavedVRegs, hsm, arm64_norm] using hvregs
      spAligned := hsp0
    }
    refine MainHops.sepWPp_weaken_pre ?_ (r1b_cleanup_2c68_placed (d := d) hh hbnd hst_m
      (by simpa [hsm, arm64_norm] using hx19) (by simpa [hsm, arm64_norm] using htrace)
      ⟨by simpa [hsm, arm64_norm] using hhist.1, by simpa [hsm, arm64_norm] using hhist.2⟩
      hans hpanic hrej)
    have hdrop_dir : ownedBytes A 0#64 d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗ anyHeap ⊢
        anyHeap := entails_anyHeap _
    refine Entails.trans (Entails.of_eq (show _ =
      runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
        storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        runSaved s0 ∗ r1b_errFrameRest fsp ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 24 ∗ memRegion (fsp + 0x188#64) 48 ∗
        memRegion (fsp + 0x1b8#64) 24 ∗ protocolAddressAt A d.peerG (fsp + 0x2a0#64) ∗
        memRegion (fsp + 0x4d0#64) 48 ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗
        (ownedBytes A 0#64 d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗ anyHeap) by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right hdrop_dir))))))))))))))))
  · have hcap_f : (d.dirCap == 0#64) = false := beq_false_of_ne hcap
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := lsρ lsRustDeallocSymCli) hinv
    (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hsm_sp : sm.sp = fsp := by simpa [hsm, arm64_norm] using hst.sp
    have hsm_fp : sm.readReg64 .fp = s0.sp - 0x60#64 := by simpa [hsm, arm64_norm] using hfp
    have hsm_vr : calleeSavedVRegs sm = calleeSavedVRegs s0 := by
      simpa [calleeSavedVRegs, hsm, arm64_norm] using hvregs
    have hsm_pc : sm.pc = lsρ lsRustDeallocSymCli := by
      simp [hsm, arm64_norm]
    have hsm_lr : sm.readReg64 .lr = runPcPlaced 0x2c68 := by
      simp [hsm, arm64_norm]
    dsimp only [fsp] at hsm_sp ⊢
    refine MainHops.sepWPp_weaken_pre (Entails.of_eq (show _ =
      ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
      stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗
      (runResAt A cliWrOk g.res (some none) ∗ memRegion g.call 56 ∗
        storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
        runSaved s0 ∗ r1b_errFrameRest (runFsp s0) ∗
        memRegion (runFsp s0 + 0x110#64) 8 ∗ memRegion (runFsp s0 + 0x11c#64) 4 ∗
        memRegion (runFsp s0 + 0x120#64) 16 ∗ memRegion (runFsp s0 + 0x150#64) 16 ∗
        memRegion (runFsp s0 + 0x168#64) 24 ∗ memRegion (runFsp s0 + 0x188#64) 48 ∗
        memRegion (runFsp s0 + 0x1b8#64) 24 ∗ protocolAddressAt A d.peerG (runFsp s0 + 0x2a0#64) ∗
        memRegion (runFsp s0 + 0x4d0#64) 48 ∗ anyHeap) by ac_rfl)) ?_
    refine r1b_call_dealloc_ownedBytes_placed (cap := d.dirCap) (ptr := d.dirPtr)
      (len := BitVec.ofNat 64 d.dir.length) (bs := d.dir) (Q := Q) hh hbnd hinv_m hsm_pc (by simp [hsm, arm64_norm, hrun])
      hsm_sp hsm_fp hsm_vr hsp0 hsm_lr
      (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
      (by simp [hsm, arm64_norm]) hcap hpanic ?_
    intro sf hin_f hcs_f hfs_f htr_f
    exact MainHops.sepWPp_weaken_pre (Entails.of_eq (by ac_rfl))
      (r1b_cleanup_2c68_placed (d := d) hh hbnd hin_f
        (hcs_f.1.trans (by simpa [hsm, arm64_norm] using hx19))
        (htr_f ▸ (by simpa [hsm, arm64_norm] using htrace))
        ⟨by rw [hfs_f]; simpa [hsm, arm64_norm] using hhist.1,
          by rw [htr_f]; simpa [hsm, arm64_norm] using hhist.2⟩
        hans
        hpanic hrej)

theorem r1b_cleanup_2c34_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2c34)
    (hpanic : PanicK g s0 Qp) (hrej : RejectKPlaced r1b_CodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r1b_errCommon A g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 24 ∗ memRegion (fsp + 0x188#64) 48 ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp (runOom s0) := by
  intro fsp
  have hfsp_eq : runFsp s0 = fsp := rfl
  dsimp only [r1b_errCommon, r1b_errCore]
  rw [hfsp_eq]
  have h1b8_24 :
      ((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr) ∗
      ((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗
      ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr) ⊢ memRegion (fsp + 0x1b8#64) 24 := by
    have hc8 : fsp + 0x1c8#64 = (fsp + 0x1c0#64) + 8#64 := by bv_omega
    have hc0 : fsp + 0x1c0#64 = (fsp + 0x1b8#64) + 8#64 := by bv_omega
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right
      (pointsTo64_entails_memRegion _ _))) ?_
    refine Entails.trans (sepConj_mono_right (by rw [hc8]; exact r1b_cell64_cons d.dirCap (by decide))) ?_
    rw [hc0]; exact r1b_cell64_cons d.meG.name.ptr (by decide)
  have hres_split : memRegion g.res runResSize =
      (∃∗ vres : BitVec 64, g.res ↦₆₄ vres) ∗ memRegion (g.res + 8#64) (runResSize - 8) := by
    conv_lhs => rw [show runResSize = 8 + (runResSize - 8) from rfl]
    rw [ProofLib.memRegion_split g.res 8 (runResSize - 8) (by decide), ProofLib.memRegion_eight]
  have hx19 := hc.x19; have hx20 := hc.x20; have hx21 := hc.x21
  have htrace := hc.trace; have hhist := hc.hist; have hans := hc.ans
  rw [hres_split]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun vres => ?_
  generalize hstP : storesAt A g.stores StoresGhost.opened = stProp
  generalize hpeerP : protocolAddressAt A d.peerG (fsp + 0x2a0#64) = peerProp
  have hpc := hc.st.pc; have hrun := hc.st.run
  have hsp : s.sp = fsp := hc.st.sp
  have hfp := hc.st.fp; have hinv := hc.st.inv; have hvregs := hc.st.vregs
  have hsp0 := hc.st.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hc.st.sp hsp0
  change s.pc = (blkPl_579).base + 0x2c34#64 at hpc
  by_cases hcap : d.meG.name.cap = 0#64
  · rw [hcap] at hx21
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := runPcPlaced 0x2c54) hinv
    rw [runPcPlaced_eq]
    (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hst_m : InRunPlaced r1b_CodeOk s0 sm 0x2c54 := {
      pc := by simp only [hsm, arm64_norm]
      run := by simp only [hsm, arm64_norm, hrun]
      sp := by simpa only [hsm, arm64_norm] using hc.st.sp
      fp := by simpa only [hsm, arm64_norm] using hfp
      inv := hinv_m
      vregs := by simpa only [calleeSavedVRegs, hsm, arm64_norm] using hvregs
      spAligned := hsp0
    }
    refine MainHops.sepWPp_weaken_pre ?_ (r1b_cleanup_2c54_placed (d := d) hh hbnd hst_m
      (by simpa only [hsm, arm64_norm] using hx19) (by simp only [hsm, arm64_norm])
      (by simp only [hsm, arm64_norm])
      (by simpa only [hsm, arm64_norm] using htrace)
      ⟨by simpa only [hsm, arm64_norm] using hhist.1,
        by simpa only [hsm, arm64_norm] using hhist.2⟩
      hans
      hpanic hrej)
    have hdrop_me : addrNameHeap A d.meG ∗ anyHeap ⊢ anyHeap := entails_anyHeap _
    dsimp only [runResAt]
    rw [hstP, hpeerP]
    dsimp only [fsp] at h1b8_24 ⊢
    refine Entails.trans (Entails.of_eq (show _ =
      ((g.res ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗
      memRegion g.call 56 ∗ stProp ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
      runSaved s0 ∗ r1b_errFrameRest (runFsp s0) ∗
      memRegion (runFsp s0 + 0x110#64) 8 ∗ memRegion (runFsp s0 + 0x11c#64) 4 ∗
      memRegion (runFsp s0 + 0x120#64) 16 ∗ memRegion (runFsp s0 + 0x150#64) 16 ∗
      memRegion (runFsp s0 + 0x168#64) 24 ∗ memRegion (runFsp s0 + 0x188#64) 48 ∗
      (((runFsp s0 + 0x1b8#64) ↦₆₄ d.meG.name.ptr) ∗ ((runFsp s0 + 0x1c0#64) ↦₆₄ d.dirCap) ∗
        ((runFsp s0 + 0x1c8#64) ↦₆₄ d.dirPtr)) ∗
      peerProp ∗ memRegion (runFsp s0 + 0x4d0#64) 48 ∗
      stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ (addrNameHeap A d.meG ∗ anyHeap) by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono h1b8_24 (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right hdrop_me)))))))))))))))))
  · have hcap_f : (d.meG.name.cap == 0#64) = false := beq_false_of_ne hcap
    apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := lsρ lsRustDeallocSymCli) hinv
    (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hsm_sp : sm.sp = fsp := by simpa only [hsm, arm64_norm] using hsp
    have hsm_fp : sm.readReg64 .fp = s0.sp - 0x60#64 := by simpa only [hsm, arm64_norm] using hfp
    have hsm_vr : calleeSavedVRegs sm = calleeSavedVRegs s0 := by
      simpa only [calleeSavedVRegs, hsm, arm64_norm] using hvregs
    have hsm_pc : sm.pc = lsρ lsRustDeallocSymCli := by
      simp only [hsm, arm64_norm]
    have hsm_lr : sm.readReg64 .lr = runPcPlaced 0x2c54 := by
      simp only [hsm, arm64_norm]
    dsimp only [fsp] at hsm_sp h1b8_24 ⊢
    apply MainHops.sepWPp_weaken_pre
    · refine Entails.trans (Entails.of_eq (show _ =
        addrNameHeap A d.meG ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗
        (((g.res ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗
          memRegion g.call 56 ∗ stProp ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
          ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
          runSaved s0 ∗ r1b_errFrameRest (runFsp s0) ∗
          memRegion (runFsp s0 + 0x110#64) 8 ∗ memRegion (runFsp s0 + 0x11c#64) 4 ∗
          memRegion (runFsp s0 + 0x120#64) 16 ∗ memRegion (runFsp s0 + 0x150#64) 16 ∗
          memRegion (runFsp s0 + 0x168#64) 24 ∗ memRegion (runFsp s0 + 0x188#64) 48 ∗
          (((runFsp s0 + 0x1b8#64) ↦₆₄ d.meG.name.ptr) ∗ ((runFsp s0 + 0x1c0#64) ↦₆₄ d.dirCap) ∗
            ((runFsp s0 + 0x1c8#64) ↦₆₄ d.dirPtr)) ∗
          peerProp ∗ memRegion (runFsp s0 + 0x4d0#64) 48 ∗
          anyHeap) by ac_rfl))
        (sepConj_mono_left (r1b_addrNameHeap_to_ownedBytes_placed A d.meG))
    refine r1b_call_dealloc_ownedBytes_placed (Q := Q) (cap := d.meG.name.cap) (ptr := d.meG.name.ptr)
      (len := BitVec.ofNat 64 d.meG.name.bytes.length) (bs := d.meG.name.bytes)
      hh hbnd hinv_m hsm_pc (by simp only [hsm, arm64_norm, hrun])
      hsm_sp hsm_fp hsm_vr hsp0 hsm_lr
      (by simp only [hsm, arm64_norm]) (by simp only [hsm, arm64_norm]) (by simp only [hsm, arm64_norm])
      hcap hpanic ?_
    intro sf hin_f hcs_f hfs_f htr_f
    refine MainHops.sepWPp_weaken_pre ?_
      (r1b_cleanup_2c54_placed (d := d) hh hbnd hin_f
        (hcs_f.1.trans (by simpa only [hsm, arm64_norm] using hx19))
        (hcs_f.2.2.2.1.trans (by simp only [hsm, arm64_norm]))
        (hcs_f.2.2.2.2.2.1.trans (by simp only [hsm, arm64_norm]))
        (htr_f ▸ (by simpa only [hsm, arm64_norm] using htrace))
        ⟨by rw [hfs_f]; simpa only [hsm, arm64_norm] using hhist.1,
          by rw [htr_f]; simpa only [hsm, arm64_norm] using hhist.2⟩
        hans
        hpanic hrej)
    dsimp only [runResAt]
    rw [hstP, hpeerP]
    refine Entails.trans (Entails.of_eq (show _ =
      ((g.res ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (g.res + 8#64) (runResSize - 8)) ∗
      memRegion g.call 56 ∗ stProp ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
      ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
      runSaved s0 ∗ r1b_errFrameRest (runFsp s0) ∗
      memRegion (runFsp s0 + 0x110#64) 8 ∗ memRegion (runFsp s0 + 0x11c#64) 4 ∗
      memRegion (runFsp s0 + 0x120#64) 16 ∗ memRegion (runFsp s0 + 0x150#64) 16 ∗
      memRegion (runFsp s0 + 0x168#64) 24 ∗ memRegion (runFsp s0 + 0x188#64) 48 ∗
      (((runFsp s0 + 0x1b8#64) ↦₆₄ d.meG.name.ptr) ∗ ((runFsp s0 + 0x1c0#64) ↦₆₄ d.dirCap) ∗
        ((runFsp s0 + 0x1c8#64) ↦₆₄ d.dirPtr)) ∗
      peerProp ∗ memRegion (runFsp s0 + 0x4d0#64) 48 ∗
      stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left h1b8_24)))))))))))))

theorem r1b_cleanup_2bf0_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A H) (hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2bf0)
    (hpanic : PanicK g s0 Qp) (hrej : RejectKPlaced r1b_CodeOk H A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r1b_SpePayload A (s.readReg64 (.gpr 12#5))
          (s.readReg64 (.gpr 9#5)) (s.readReg64 (.gpr 23#5))
          (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
          (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
          (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 22#5)) ∗
        r1b_errCommon A g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 24 ∗ memRegion (fsp + 0x188#64) 48 ∗
        memRegion (fsp + 0x4d0#64) 48)
      Q Qp (runOom s0) := by
  intro fsp
  have hfsp_eq : runFsp s0 = fsp := rfl
  dsimp only [r1b_errCommon]
  generalize herrCore : r1b_errCore A g d s0 = errCore
  rw [hfsp_eq]
  rw [r1b_region48_to_cells (fsp + 0x4d0#64)]
  simp only [sepExists_sepConj_right]
  refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun w1 =>
    SepWPp.exists_elim fun w2 => SepWPp.exists_elim fun w3 =>
    SepWPp.exists_elim fun w4 => SepWPp.exists_elim fun w5 => ?_
  have ho8 : fsp + 0x4d0#64 + 8#64 = fsp + 0x4d8#64 := by bv_omega
  have ho16 : fsp + 0x4d0#64 + 16#64 = fsp + 0x4e0#64 := by bv_omega
  have ho24 : fsp + 0x4d0#64 + 24#64 = fsp + 0x4e8#64 := by bv_omega
  have ho32 : fsp + 0x4d0#64 + 32#64 = fsp + 0x4f0#64 := by bv_omega
  have ho40 : fsp + 0x4d0#64 + 40#64 = fsp + 0x4f8#64 := by bv_omega
  rw [ho8, ho16, ho24, ho32, ho40]
  apply MainHops.sepWPp_weaken_pre
  · exact Entails.of_eq (show _ =
      (r1b_SpePayload A (s.readReg64 (.gpr 12#5))
          (s.readReg64 (.gpr 9#5)) (s.readReg64 (.gpr 23#5))
          (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
          (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
          (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 22#5)) ∗
        ((fsp + 0x4d0#64) ↦₆₄ w0 ∗ (fsp + 0x4d8#64) ↦₆₄ w1 ∗
          (fsp + 0x4e0#64) ↦₆₄ w2 ∗ (fsp + 0x4e8#64) ↦₆₄ w3 ∗
          (fsp + 0x4f0#64) ↦₆₄ w4 ∗ (fsp + 0x4f8#64) ↦₆₄ w5)) ∗
      (errCore ∗ stackAt fsp (resStack - runFrame) ∗ A.pool ∗ anyHeap ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 24 ∗ memRegion (fsp + 0x188#64) 48) by ac_rfl)
  have hpc := hc.st.pc; have hrun := hc.st.run
  have hsp : s.sp = fsp := hc.st.sp
  have hfp := hc.st.fp; have hinv := hc.st.inv; have hvregs := hc.st.vregs
  have hsp0 := hc.st.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hc.st.sp hsp0
  change s.pc = (blkPl_579).base + 0x2bf0#64 at hpc
  apply LibsignalPublicApi.StoreKit.sepWPp_seq_lscro (mid := lsmpl.base 553) hinv
  (try dsimp only [runProgPlaced, lsProg_579]); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
  change SepWPp (runProgPlaced H) _ _ _ _ _ _
  have hsm_sp : sm.sp = fsp := by simpa only [hsm, arm64_norm] using hsp
  have hsm_fp : sm.readReg64 .fp = s0.sp - 0x60#64 := by simpa only [hsm, arm64_norm] using hfp
  have hsm_vr : calleeSavedVRegs sm = calleeSavedVRegs s0 := by
    simpa only [calleeSavedVRegs, hsm, arm64_norm] using hvregs
  have hsm_pc : sm.pc = lsmpl.base 553 := by
    simp only [hsm, arm64_norm]
  have hsm_lr : sm.readReg64 .lr = runPcPlaced 0x2c34 := by
    simp only [hsm, arm64_norm]
  have hpack_all : ∀ w1' w2' w3' : BitVec 64,
      w1' = ((s.readReg64 (.gpr 9#5) &&& 0xffffffff#64) ||| (s.readReg64 (.gpr 23#5) <<< 32)) →
      w2' = ((s.readReg64 (.gpr 27#5) &&& 0x00ffffffffffffff#64) |||
        ((s.readReg64 (.gpr 16#5) &&& 0xff#64) <<< 56)) →
      w3' = ((((s.readReg64 (.gpr 14#5) &&& 16777215#64) <<< 32) |||
        (s.readReg64 (.gpr 28#5) <<< 56)) |||
        (((s.readReg64 (.gpr 15#5) <<< 8) &&& 0xffffff00#64) |||
          (s.readReg64 (.gpr 22#5) &&& 0xff#64))) →
      r1b_SpePayload A (s.readReg64 (.gpr 12#5))
        (s.readReg64 (.gpr 9#5)) (s.readReg64 (.gpr 23#5))
        (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
        (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
        (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 22#5)) ∗
      ((fsp + 0x4d0#64) ↦₆₄ s.readReg64 (.gpr 12#5) ∗
        (fsp + 0x4d8#64) ↦₆₄ w1' ∗ (fsp + 0x4e0#64) ↦₆₄ w2' ∗
        (fsp + 0x4e8#64) ↦₆₄ w3' ∗ (fsp + 0x4f0#64) ↦₆₄ s.readReg64 (.gpr 11#5) ∗
        (fsp + 0x4f8#64) ↦₆₄ s.readReg64 (.gpr 13#5)) ⊢
      ∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A (fsp + 0x4d0#64) k := by
    intro w1' w2' w3' h1 h2 h3
    have hp := r1b_pack_speOwnedAt A (fsp + 0x4d0#64) (s.readReg64 (.gpr 12#5))
      w1' w2' w3' (s.readReg64 (.gpr 11#5)) (s.readReg64 (.gpr 13#5))
      (s.readReg64 (.gpr 9#5)) (s.readReg64 (.gpr 23#5))
      (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
      (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
      (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 22#5)) h1 h2 h3
    rw [ho8, ho16, ho24, ho32, ho40] at hp
    exact hp
  apply MainHops.sepWPp_weaken_pre
  · exact sepConj_mono_left (hpack_all _ _ _ (by bv_bits) (by bv_bits) (by bv_bits))
  rw [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun k => ?_
  dsimp only [fsp] at hsm_sp ⊢
  refine MainHops.sepWPp_weaken_pre (Entails.of_eq (show _ =
    RunDrop.speOwnedAt A (runFsp s0 + 0x4d0#64) k ∗
    stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗
    (errCore ∗ anyHeap ∗ memRegion (runFsp s0 + 0x110#64) 8 ∗ memRegion (runFsp s0 + 0x11c#64) 4 ∗
      memRegion (runFsp s0 + 0x120#64) 16 ∗ memRegion (runFsp s0 + 0x150#64) 16 ∗
      memRegion (runFsp s0 + 0x168#64) 24 ∗ memRegion (runFsp s0 + 0x188#64) 48) by ac_rfl)) ?_
  refine r1b_call_dropSpeOwned_placed (a := runFsp s0 + 0x4d0#64) (k := k) (Q := Q) hh hdrop hbnd hinv_m hsm_pc (by simp only [hsm, arm64_norm, hrun])
    hsm_sp hsm_fp hsm_vr hsp0 hsm_lr
    (by simp only [hsm, arm64_norm]; dsimp only [fsp, runFsp, runFrame]; bv_omega) hpanic ?_
  intro sf hin_f hcs_f hfs_f htr_f
  have hc_f : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sf 0x2c34 := {
    st := hin_f
    x19 := hcs_f.1.trans (by simpa only [hsm, arm64_norm] using hc.x19)
    x20 := hcs_f.2.1.trans (by simpa only [hsm, arm64_norm] using hc.x20)
    x21 := hcs_f.2.2.1.trans (by simpa only [hsm, arm64_norm] using hc.x21)
    trace := htr_f ▸ (by simpa only [hsm, arm64_norm] using hc.trace)
    hist := ⟨by rw [hfs_f]; simpa only [hsm, arm64_norm] using hc.hist.1,
      by rw [htr_f]; simpa only [hsm, arm64_norm] using hc.hist.2⟩
    ans := hc.ans
  }
  refine MainHops.sepWPp_weaken_pre ?_ (r1b_cleanup_2c34_placed hh hbnd hc_f hpanic hrej)
  dsimp only [r1b_errCommon]
  rw [herrCore]
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SignalSession.Cli.RunCompose
