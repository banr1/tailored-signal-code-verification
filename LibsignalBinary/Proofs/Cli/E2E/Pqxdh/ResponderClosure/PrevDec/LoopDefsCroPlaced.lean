/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefsPlaced
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Fixed-`ext` `LibsignalCodeRoLoaded` Loop Definitions

Pointwise (`ext`-fixed) `[LibsignalPlacement]` loop and step contracts threading
`StoreKit.LibsignalCodeRoLoaded lsmpl` across `(blkPl_518).base + 0x1ee8 → +0x2620` on
`lsProg_518 ext`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Arm64 ProofLib ProofLib.ObjectLoad SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (PanicOomProp)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure (decryptPrekeyClosureName)
open CryptoVerification.E2E.Record.DeserializeGeneral (GenField)
open Symbolic.Swarm.TRREF.B3DeserQ (SSGQ GenFieldQ prostSSGQAt ssgqOf genFieldsQ)
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.LibsignalPublicApi

/-- Lift any `SepWPp` by threading `StoreKit.LibsignalCodeRoLoaded lsmpl` via `Steps.keepsFrozen`. -/
theorem sepWPp_lift_cro [LibsignalPlacement] {prog : Program} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hwp : SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s P
      (fun sf P_f => StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ Q sf P_f) Qp := by
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hQ⟩ | hpan⟩ := hwp R hm hL
  · exact ⟨sf, hsteps, .inl ⟨hpc, hrun, P_f, hmf, hcro.of_keepsFrozen hsteps.keepsFrozen, hQ⟩⟩
  · exact ⟨sf, hsteps, .inr hpan⟩

/-- Fixed-`ext` `[LibsignalPlacement]` inlined `SessionStructure::decode` of `enc`
(`(blkPl_518).base + 0x1ee8 → (blkPl_518).base + 0x2620`, closure frame `s.sp`) on `lsProg_518 ext`
under `StoreKit.LibsignalCodeRoLoaded lsmpl`. -/
def OverPrevDecodeCroPlacedAt [LibsignalPlacement]
    (ext : String → Option (State → State)) : Prop :=
  ∀ (s0 s : State) (prevCap prevPtr encCap encPtr : BitVec 64) (enc : List (BitVec 8))
    (sess : Session (List (BitVec 8))),
    OverPrevEncOKAt enc sess →
    StoreKit.LibsignalCodeRoLoaded lsmpl s.mem →
    (lsProg_518 ext).CodeLoaded s.mem →
    s.pc = (blkPl_518).base + 0x1ee8#64 →
    s.status = .Running →
    (s.sp &&& 15#64 == 0#64) = true →
    s.trace = s0.trace →
    s.readReg64 .x21 = s.sp + 0x930#64 →
    s.readReg64 .x24 = 1#64 →
    s.readReg64 .x25 = 0xffffffffffffffff#64 →
    s.readReg64 .x27 = prevPtr →
    s.readReg64 .x29 = s.sp + 0xc70#64 →
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2620#64) s
      (overPrevElemAt prevCap prevPtr encCap encPtr enc ∗ overDecScratchPre s.sp ∗
        stackAt s.sp overDecStackX ∗
        CryptoVerification.E2E.Record.A0.pool)
      (fun sf P_f =>
        (P_f ⊢ overPrevElemAt prevCap prevPtr encCap encPtr enc ∗
            overDecScratchPost s.sp (ssgqOf sess) ∗
            stackAt s.sp overDecStackX ∗
            CryptoVerification.E2E.Record.A0.pool ∗ anyHeap) ∧
        sf.sp = s.sp ∧ sf.trace = s0.trace ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧
        (lsProg_518 ext).CodeLoaded sf.mem ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.sp + 0x930#64 ∧ sf.readReg64 .x24 = 1#64 ∧
        sf.readReg64 .x25 = 0xffffffffffffffff#64 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = prevPtr ∧ sf.readReg64 .x29 = s.sp + 0xc70#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s)
      (PanicOomProp s0)

/-- Register and machine-state invariant at `(blkPl_518).base + off` inside the decode loop
under `[LibsignalPlacement]` with `StoreKit.LibsignalCodeRoLoaded lsmpl`. -/
def OverDecRegsCroPlaced [LibsignalPlacement] (ext : String → Option (State → State)) (s0 : State)
    (g : OverDecG) (off : BitVec 64) (s : State) : Prop :=
  StoreKit.LibsignalCodeRoLoaded lsmpl s.mem ∧ OverDecRegsPlaced ext s0 g off s

theorem sepWPp_lift_cro_regs [LibsignalPlacement] {ext : String → Option (State → State)}
    {ret off : BitVec 64} {s0 s : State} {g : OverDecG} {P : SepProp}
    {Rpost : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hwp : SepWPp (lsProg_518 ext) ret s P
      (fun sf P_f => OverDecRegsPlaced ext s0 g off sf ∧ Rpost sf P_f)
      (PanicOomProp s0)) :
    SepWPp (lsProg_518 ext) ret s P
      (fun sf P_f => OverDecRegsCroPlaced ext s0 g off sf ∧ Rpost sf P_f)
      (PanicOomProp s0) := by
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hregs, hR⟩ | hpan⟩ := hwp R hm hL
  · exact ⟨sf, hsteps, .inl ⟨hpc, hrun, P_f, hmf,
      ⟨hcro.of_keepsFrozen hsteps.keepsFrozen, hregs⟩, hR⟩⟩
  · exact ⟨sf, hsteps, .inr hpan⟩

/-- Fixed-`ext` `LibsignalCodeRoLoaded` Entry (`+0x1ee8 → +0x216c`). -/
def OverDecEntryCroPlacedAt [LibsignalPlacement] (ext : String → Option (State → State)) : Prop :=
  ∀ (s0 s : State) (g : OverDecG),
    g.enc ≠ [] → g.enc.length < 2 ^ 62 →
    StoreKit.LibsignalCodeRoLoaded lsmpl s.mem →
    (lsProg_518 ext).CodeLoaded s.mem →
    s.pc = (blkPl_518).base + 0x1ee8#64 →
    s.status = .Running → s.sp = g.q → (s.sp &&& 15#64 == 0#64) = true →
    s.trace = s0.trace →
    s.readReg64 .x19 = g.r19 → s.readReg64 .x20 = g.r20 → s.readReg64 .x26 = g.r26 →
    s.readReg64 .x21 = g.q + 0x930#64 → s.readReg64 .x24 = 1#64 →
    s.readReg64 .x25 = 0xffffffffffffffff#64 → s.readReg64 .x27 = g.prevPtr →
    s.readReg64 .x29 = g.q + 0xc70#64 →
    calleeSavedVRegs s = calleeSavedVRegs g.sv →
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x216c#64) s
      (overPrevElemAt g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗ overDecScratchPre g.q ∗
        stackAt g.q overDecStackX ∗
        CryptoVerification.E2E.Record.A0.pool)
      (fun sf P_f => OverDecRegsCroPlaced ext s0 g 0x216c#64 sf ∧
        (P_f ⊢ overDecHeap g g.enc SSGQ.empty))
      (PanicOomProp s0)

/-- Fixed-`ext` `LibsignalCodeRoLoaded` one field (`+0x216c → +0x2160`) restricted by `P`. -/
def OverDecFieldCroPlacedAt [LibsignalPlacement] (ext : String → Option (State → State))
    (P : GenFieldQ → Prop) : Prop :=
  ∀ (s0 s : State) (g : OverDecG) (v : SSGQ) (fl : GenFieldQ) (rest : List (BitVec 8)),
    P fl → fl.Ok → fl.Fresh v →
    (fl.enc ++ rest) <:+ g.enc → g.enc.length < 2 ^ 62 →
    OverDecRegsCroPlaced ext s0 g 0x216c#64 s →
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2160#64) s
      (overDecHeap g (fl.enc ++ rest) v)
      (fun sf P_f => OverDecRegsCroPlaced ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ overDecHeap g rest (v.apply fl)))
      (PanicOomProp s0)

/-- Fixed-`ext` `LibsignalCodeRoLoaded` loop head (`+0x2160 → +0x216c`) when `rest ≠ []`. -/
def OverDecHeadConsCroPlacedAt [LibsignalPlacement]
    (ext : String → Option (State → State)) : Prop :=
  ∀ (s0 s : State) (g : OverDecG) (v : SSGQ) (rest : List (BitVec 8)),
    rest ≠ [] → rest <:+ g.enc → g.enc.length < 2 ^ 62 →
    OverDecRegsCroPlaced ext s0 g 0x2160#64 s →
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x216c#64) s
      (overDecHeap g rest v)
      (fun sf P_f => OverDecRegsCroPlaced ext s0 g 0x216c#64 sf ∧ (P_f ⊢ overDecHeap g rest v))
      (PanicOomProp s0)

/-- Fixed-`ext` `LibsignalCodeRoLoaded` loop head (`+0x2160 → +0x2620`) when `rest = []`. -/
def OverDecHeadNilCroPlacedAt [LibsignalPlacement]
    (ext : String → Option (State → State)) : Prop :=
  ∀ (s0 s : State) (g : OverDecG) (v : SSGQ),
    g.enc.length < 2 ^ 62 →
    OverDecRegsCroPlaced ext s0 g 0x2160#64 s →
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2620#64) s
      (overDecHeap g [] v)
      (fun sf P_f => OverDecRegsCroPlaced ext s0 g 0x2620#64 sf ∧ (P_f ⊢ overDecHeap g [] v))
      (PanicOomProp s0)

/-- Fixed-`ext` `LibsignalCodeRoLoaded` Key (`+0x216c → overDecArmOff fl`). -/
def OverDecKeyCroPlacedAt [LibsignalPlacement] (ext : String → Option (State → State)) : Prop :=
  ∀ (s0 s : State) (g : OverDecG) (v : SSGQ) (fl : GenFieldQ) (rest : List (BitVec 8)),
    OverDecAnyField fl → fl.Ok →
    (fl.enc ++ rest) <:+ g.enc → g.enc.length < 2 ^ 62 →
    OverDecRegsCroPlaced ext s0 g 0x216c#64 s →
    SepWPp (lsProg_518 ext) ((blkPl_518).base + overDecArmOff fl) s
      (overDecHeap g (fl.enc ++ rest) v)
      (fun sf P_f => OverDecRegsCroPlaced ext s0 g (overDecArmOff fl) sf ∧
        sf.readReg64 .x0 = overDecWt fl ∧
        sf.readReg64 .x22 = BitVec.ofNat 64 (fl.tag * 8 + (overDecWt fl).toNat) ∧
        (P_f ⊢ overDecHeap g (fl.payload ++ rest) v))
      (PanicOomProp s0)

/-- Fixed-`ext` `LibsignalCodeRoLoaded` Arm contract (`overDecArmOff fl → +0x2160`). -/
def OverDecArmCroPlacedAt [LibsignalPlacement] (ext : String → Option (State → State))
    (P : GenFieldQ → Prop) : Prop :=
  ∀ (s0 s : State) (g : OverDecG) (v : SSGQ) (fl : GenFieldQ) (rest : List (BitVec 8)),
    P fl → fl.Ok → fl.Fresh v →
    (fl.enc ++ rest) <:+ g.enc → g.enc.length < 2 ^ 62 →
    OverDecRegsCroPlaced ext s0 g (overDecArmOff fl) s →
    s.readReg64 .x0 = overDecWt fl →
    s.readReg64 .x22 = BitVec.ofNat 64 (fl.tag * 8 + (overDecWt fl).toNat) →
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2160#64) s
      (overDecHeap g (fl.payload ++ rest) v)
      (fun sf P_f => OverDecRegsCroPlaced ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ overDecHeap g rest (v.apply fl)))
      (PanicOomProp s0)

abbrev OverDecArmCroPlacedAtTR [LibsignalPlacement] (ext : String → Option (State → State))
    (P : GenFieldQ → Prop) : Prop :=
  OverDecArmCroPlacedAt ext P

theorem overDecEntry_cro_of_placed [LibsignalPlacement] (h : OverDecEntryPlacedStmt)
    (ext : String → Option (State → State)) : OverDecEntryCroPlacedAt ext := by
  intro s0 s g hne hlen hcro hcl hpc hrun hsp hal htr h19 h20 h26 h21 h24 h25 h27 h29 hv
  exact sepWPp_lift_cro_regs hcro
    (h ext s0 s g hne hlen hcl hpc hrun hsp hal htr h19 h20 h26 h21 h24 h25 h27 h29 hv)

theorem overDecHeadCons_cro_of_placed [LibsignalPlacement] (h : OverDecHeadConsPlacedStmt)
    (ext : String → Option (State → State)) : OverDecHeadConsCroPlacedAt ext := by
  intro s0 s g v rest hne hsuf hlen ⟨hcro, hregs⟩
  exact sepWPp_lift_cro_regs hcro (h ext s0 s g v rest hne hsuf hlen hregs)

theorem overDecHeadNil_cro_of_placed [LibsignalPlacement] (h : OverDecHeadNilPlacedStmt)
    (ext : String → Option (State → State)) : OverDecHeadNilCroPlacedAt ext := by
  intro s0 s g v hlen ⟨hcro, hregs⟩
  exact sepWPp_lift_cro_regs hcro (h ext s0 s g v hlen hregs)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
