/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.FsTrace
public import ProofLib.Process
public import ProofLib.SepLogic.WP.StepsSubword
public import ProofLib.SepLogic.WP.Syscalls
public import ProofLib.SyscallModels
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Process-Startup and Exit Syscall `SepWP` Step Lemmas

`SepWP` step lemmas for Linux process-startup and exit syscalls (`set_tid_address`, `ppoll`,
`sigaltstack`, `rt_sigaction`, and `exit_group`).
-/

set_option autoImplicit false

@[expose] public section

namespace ProofLib

open Arm64

/-- `SVC #0` rule for `set_tid_address` (`X8 = 96`): writes `SIM_TID` (`1`) to `X0` and advances
    `pc` by `4`, preserving memory and all process fields. -/
theorem SepWP.step_svc_set_tid_address {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 96#64)
    (hexec : (s.writeReg64 .x0 SIM_TID).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execSetTidAddress s := by
      simp [wp_norm, arm64_norm, Reg.x8, *]) :
    SepWP prog target_pc s P post oom := by
  let _ := hx8
  have hpc_eq : s.setPC pc = s := by cases s; simp [State.setPC] at hpc ⊢; exact hpc.symm
  refine SepWP.step_pure hpc hrun hfetch ?_ ?_ hnext
  · rw [hpc_eq, ← hexec, hsvc]
    cases s; simp [execSetTidAddress, State.writeReg64, State.advancePC, State.setPC, hpc]
  · rw [← hexec]; cases s; rfl

/-- Pure byte-slice counterpart of `evalPpollEntries` over `8 * nfds` bytes of `struct pollfd`. -/
def evalPpollBytes (fs : FsState) : List (BitVec 8) → Nat → Option (List (BitVec 8) × Nat)
  | [], count => some ([], count)
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: _ :: _ :: rest, count =>
    let fd : BitVec 32 := b3 ++ b2 ++ b1 ++ b0
    let events : BitVec 16 := b5 ++ b4
    if (fd != 0#32 && fd != 1#32 && fd != 2#32) || events != 0#16 then none
    else match fs.fds (fd.zeroExtend 64) with
      | none =>
        (evalPpollBytes fs rest (count + 1)).map fun (bs', c') =>
          (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: 0x20#8 :: 0#8 :: bs', c')
      | some desc =>
        if desc.kind == .stdio || desc.kind == .localFile then
          (evalPpollBytes fs rest count).map fun (bs', c') =>
            (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: 0#8 :: 0#8 :: bs', c')
        else none
  | _, _ => none

theorem evalPpollEntries_of_bytes (fs : FsState) :
    ∀ (rem idx count : Nat) (ufds : BitVec 64) (m : Memory) (bs bs' : List (BitVec 8)) (c' : Nat)
      (R : SepProp),
      bs.length = rem * 8 →
      m ⊨ ((ufds + BitVec.ofNat 64 (idx * 8)) ↦ₛ bs) ∗ R →
      evalPpollBytes fs bs count = some (bs', c') →
      ∃ m', evalPpollEntries fs m ufds rem idx count = some (m', c') ∧
        m' ⊨ ((ufds + BitVec.ofNat 64 (idx * 8)) ↦ₛ bs') ∗ R := by
  intro rem
  induction rem with
  | zero =>
    intro idx count ufds m bs bs' c' R hlen hm hev
    cases bs with
    | nil =>
      simp only [evalPpollBytes, Option.some.injEq, Prod.mk.injEq] at hev
      rcases hev with ⟨rfl, rfl⟩; exact ⟨m, rfl, hm⟩
    | cons _ _ => simp at hlen
  | succ rem ih =>
    intro idx count ufds m bs bs' c' R hlen hm hev
    rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, rest⟩⟩⟩⟩⟩⟩⟩⟩ <;>
      try (simp only [List.length_cons, List.length_nil] at hlen; omega)
    have hrest_len : rest.length = rem * 8 := by simp only [List.length_cons] at hlen; omega
    let entry := ufds + BitVec.ofNat 64 (idx * 8)
    have hsplit : ∀ (r0 r1 : BitVec 8) (tl : List (BitVec 8)),
        (entry ↦ₛ (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: r0 :: r1 :: tl)) =
          ((entry ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗ (((entry + 4#64) ↦₁₆ (b5 ++ b4)) ∗
            (((entry + 6#64) ↦₁₆ (r1 ++ r0)) ∗ ((entry + 8#64) ↦ₛ tl)))) := by
      intro r0 r1 tl
      have h8 : b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: r0 :: r1 :: tl =
          ([b0, b1] ++ [b2, b3]) ++ ([b4, b5] ++ ([r0, r1] ++ tl)) := rfl
      rw [h8, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append]
      simp only [List.length_append, List.length_cons, List.length_nil, pointsToBytes2_eq_pointsTo16]
      have ha2 : (BitVec.ofNat 64 2 : BitVec 64) = 2#64 := rfl
      have ha4 : (BitVec.ofNat 64 4 : BitVec 64) = 4#64 := rfl
      have ha6 : entry + 4#64 + 2#64 = entry + 6#64 := by bv_omega
      have ha8 : entry + 6#64 + 2#64 = entry + 8#64 := by bv_omega
      have hb32 : ((b3 ++ b2) ++ (b1 ++ b0) : BitVec 32) = b3 ++ b2 ++ b1 ++ b0 := by bv_bits
      rw [ha2, ha4, pointsTo16_pair, hb32, ha6, ha8]
    change m ⊨ (entry ↦ₛ _) ∗ R at hm; rw [hsplit b6 b7 rest] at hm
    have hm_fd : m ⊨ (entry ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
        (((entry + 4#64) ↦₁₆ (b5 ++ b4)) ∗ (((entry + 6#64) ↦₁₆ (b7 ++ b6)) ∗ ((entry + 8#64) ↦ₛ rest)) ∗ R) := by
      ac_nf at hm ⊢
    have hrd_fd : m.read32 entry = b3 ++ b2 ++ b1 ++ b0 := (IsBlock.pointsTo32 _ _).read hm_fd
    have hm_ev : m ⊨ ((entry + 4#64) ↦₁₆ (b5 ++ b4)) ∗ ((entry ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
        (((entry + 6#64) ↦₁₆ (b7 ++ b6)) ∗ ((entry + 8#64) ↦ₛ rest)) ∗ R) := by ac_nf at hm ⊢
    have hrd_ev : m.read16 (entry + 4#64) = b5 ++ b4 := (IsBlock.pointsTo16 _ _).read hm_ev
    have hm_rev : m ⊨ ((entry + 6#64) ↦₁₆ (b7 ++ b6)) ∗
        (((entry + 8#64) ↦ₛ rest) ∗ ((entry ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗ ((entry + 4#64) ↦₁₆ (b5 ++ b4)) ∗ R)) := by
      ac_nf at hm ⊢
    have hentry8 : entry + 8#64 = ufds + BitVec.ofNat 64 ((idx + 1) * 8) := by dsimp [entry]; bv_omega
    dsimp only [evalPpollBytes] at hev; dsimp only [evalPpollEntries]
    rw [show m.read32 (ufds + BitVec.ofNat 64 (idx * 8)) = b3 ++ b2 ++ b1 ++ b0 from hrd_fd,
        show m.read16 (ufds + BitVec.ofNat 64 (idx * 8) + 4#64) = b5 ++ b4 from hrd_ev]
    split at hev
    · simp at hev
    · next hok =>
      simp only [hok, Bool.false_eq_true, ↓reduceIte]
      cases hfd : fs.fds ((b3 ++ b2 ++ b1 ++ b0 : BitVec 32).zeroExtend 64) with
      | none =>
        rw [hfd] at hev; dsimp only at hev
        rcases Option.map_eq_some_iff.mp hev with ⟨⟨tl', c''⟩, hev_rest, hpair⟩
        rcases Prod.mk.inj hpair with ⟨hbs, rfl⟩; subst hbs
        have hm1 := (IsBlock.pointsTo16 (entry + 6#64) (b7 ++ b6)).write16 hm_rev POLLNVAL
        have hm1' : m.write16 (entry + 6#64) POLLNVAL ⊨ ((ufds + BitVec.ofNat 64 ((idx + 1) * 8)) ↦ₛ rest) ∗
            (((entry ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗ ((entry + 4#64) ↦₁₆ (b5 ++ b4)) ∗
              ((entry + 6#64) ↦₁₆ (0#8 ++ 0x20#8))) ∗ R) := by
          rw [← hentry8]; change _ ⊨ _ at hm1
          have hp : POLLNVAL = 0#8 ++ 0x20#8 := rfl
          rw [hp] at hm1; ac_nf at hm1 ⊢
        rcases ih (idx + 1) (count + 1) ufds _ rest tl' c'' _ hrest_len hm1' hev_rest with ⟨m', heval', hm'⟩
        refine ⟨m', heval', ?_⟩
        rw [← hentry8] at hm'; change m' ⊨ (entry ↦ₛ _) ∗ R
        rw [hsplit 0x20#8 0#8 tl']; ac_nf at hm' ⊢
      | some desc =>
        rw [hfd] at hev; dsimp only at hev
        split at hev
        · next hkind =>
          simp only [hkind, ↓reduceIte]
          rcases Option.map_eq_some_iff.mp hev with ⟨⟨tl', c''⟩, hev_rest, hpair⟩
          rcases Prod.mk.inj hpair with ⟨hbs, rfl⟩; subst hbs
          have hm1 := (IsBlock.pointsTo16 (entry + 6#64) (b7 ++ b6)).write16 hm_rev 0#16
          have hm1' : m.write16 (entry + 6#64) 0#16 ⊨ ((ufds + BitVec.ofNat 64 ((idx + 1) * 8)) ↦ₛ rest) ∗
              (((entry ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗ ((entry + 4#64) ↦₁₆ (b5 ++ b4)) ∗
                ((entry + 6#64) ↦₁₆ (0#8 ++ 0#8))) ∗ R) := by
            rw [← hentry8]
            have hp : (0#16 : BitVec 16) = 0#8 ++ 0#8 := rfl
            rw [hp] at hm1; ac_nf at hm1 ⊢
          rcases ih (idx + 1) count ufds _ rest tl' c'' _ hrest_len hm1' hev_rest with ⟨m', heval', hm'⟩
          refine ⟨m', heval', ?_⟩
          rw [← hentry8] at hm'; change m' ⊨ (entry ↦ₛ _) ∗ R
          rw [hsplit 0#8 0#8 tl']; ac_nf at hm' ⊢
        · simp at hev

/-- `SVC #0` rule for non-blocking `ppoll(ufds, nfds, tsp, 0)` (`X8 = 73`) with zero timeout
    `((tsp ↦₆₄ 0#64) ∗ ((tsp + 8#64) ↦₆₄ 0#64))`. -/
theorem SepWP.step_svc_ppoll {prog : Program} {target_pc : BitVec 64}
    {s : State} {ufds tsp : BitVec 64} {nfds count : Nat} {bs₀ bs' : List (BitVec 8)} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} {pc : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 73#64)
    (hufds : s.readReg64 .x0 = ufds) (hnfds : (s.readReg32 .x1).toNat = nfds)
    (htsp : s.readReg64 .x2 = tsp) (hsigmask : s.readReg64 .x3 = 0#64)
    (htspNe : tsp ≠ 0#64) (htspFit : tsp.toNat + 16 ≤ 2 ^ 64)
    (hnfdsMax : nfds ≤ FsState.maxOpenFds) (hufdsFit : ufds.toNat + nfds * 8 ≤ 2 ^ 64)
    (hlen : bs₀.length = nfds * 8)
    (heval : evalPpollBytes s.fs bs₀ 0 = some (bs', count))
    (hnext : ∀ m' : Memory,
      SepWP prog target_pc (((s.setMem m').writeReg64 .x0 (BitVec.ofNat 64 count)).setPC (pc + 4#64))
        ((ufds ↦ₛ bs') ∗ (((tsp ↦₆₄ 0#64) ∗ ((tsp + 8#64) ↦₆₄ 0#64)) ∗ F)) post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execPpoll s := by
      simp [wp_norm, arm64_norm, Reg.x8, *]) :
    SepWP prog target_pc s
      ((ufds ↦ₛ bs₀) ∗ (((tsp ↦₆₄ 0#64) ∗ ((tsp + 8#64) ↦₆₄ 0#64)) ∗ F)) post oom := by
  let _ := hx8
  intro R hm
  have hm_u : s.mem ⊨ ((ufds + BitVec.ofNat 64 (0 * 8)) ↦ₛ bs₀) ∗
      ((((tsp ↦₆₄ 0#64) ∗ ((tsp + 8#64) ↦₆₄ 0#64)) ∗ F) ∗ R) := by
    have hz : ufds + BitVec.ofNat 64 (0 * 8) = ufds := by simp
    rw [hz, ← sepConj_assoc]; exact hm
  have hm_u0 : s.mem ⊨ (ufds ↦ₛ bs₀) ∗ ((((tsp ↦₆₄ 0#64) ∗ ((tsp + 8#64) ↦₆₄ 0#64)) ∗ F) ∗ R) := by
    rw [← sepConj_assoc]; exact hm
  have hufdsRead : s.mem.canRead ufds (nfds * 8) = true :=
    hlen ▸ (IsBlock.pointsToBytes ufds bs₀).canRead ((IsBlock.pointsToBytes ufds bs₀).read hm_u0).1 hm_u0
  have hufdsWrite : s.mem.canWrite ufds (nfds * 8) = true :=
    hlen ▸ (IsBlock.pointsToBytes ufds bs₀).canWrite ((IsBlock.pointsToBytes ufds bs₀).read hm_u0).1 hm_u0
  have hm_ts1 : s.mem ⊨ (tsp ↦₆₄ 0#64) ∗ (((tsp + 8#64) ↦₆₄ 0#64) ∗ ((ufds ↦ₛ bs₀) ∗ F ∗ R)) := by
    ac_nf at hm ⊢
  have hm_ts2 : s.mem ⊨ ((tsp + 8#64) ↦₆₄ 0#64) ∗ ((tsp ↦₆₄ 0#64) ∗ ((ufds ↦ₛ bs₀) ∗ F ∗ R)) := by
    ac_nf at hm ⊢
  have htvSec : s.mem.read64 tsp = 0#64 := (IsBlock.pointsTo64 tsp 0#64).read hm_ts1
  have htvNsec : s.mem.read64 (tsp + 8#64) = 0#64 := (IsBlock.pointsTo64 (tsp + 8#64) 0#64).read hm_ts2
  have hm_ts16 : s.mem ⊨ (tsp ↦ₛ (unpack64 0#64 ++ unpack64 0#64)) ∗ ((ufds ↦ₛ bs₀) ∗ F ∗ R) := by
    rw [pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes,
      ← pointsTo64_eq_pointsToBytes]; ac_nf at hm ⊢
  have htspRead : s.mem.canRead tsp 16 = true :=
    (IsBlock.pointsToBytes tsp (unpack64 0#64 ++ unpack64 0#64)).canRead (by decide) hm_ts16
  rcases evalPpollEntries_of_bytes s.fs nfds 0 0 ufds s.mem bs₀ bs' count _ hlen hm_u heval with
    ⟨m', heval_m, hm'⟩
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  rw [hsvc, execPpoll_ok s hsigmask (htsp ▸ htspNe) (htsp ▸ htspFit) (htsp ▸ htspRead)
    (htsp ▸ htvSec) (htsp ▸ htvNsec) (hnfds ▸ hnfdsMax) (by rw [hufds, hnfds]; exact hufdsFit)
    (by rw [hufds, hnfds]; exact hufdsRead) (by rw [hufds, hnfds]; exact hufdsWrite)
    (by rw [hufds, hnfds]; exact heval_m)]
  have hst : ((s.setMem m').writeReg64 .x0 (BitVec.ofNat 64 count)).advancePC =
      (((s.setMem m').writeReg64 .x0 (BitVec.ofNat 64 count)).setPC (pc + 4#64)) := by
    cases s; simp [State.setMem, State.writeReg64, State.advancePC, State.setPC, hpc]
  rw [hst]
  apply hnext m' R
  have hz : ufds + BitVec.ofNat 64 (0 * 8) = ufds := by simp
  rw [hz] at hm'
  change m' ⊨ _
  ac_nf at hm' ⊢

/-- Optional 24-byte input `stack_t` at `uss` (`emp` when `uss == 0`, otherwise
    `ss_sp : u64` at `+0`, `ss_flags : u32` at `+8`, 4-byte caller padding at `+12`,
    `ss_size : u64` at `+16`). -/
def stackTAt (uss ssSp : BitVec 64) (ssFlags pad : BitVec 32) (ssSize : BitVec 64) : SepProp :=
  if uss == 0#64 then emp
  else ((uss ↦₆₄ ssSp) ∗ ((uss + 8#64) ↦₃₂ ssFlags) ∗
    ((uss + 12#64) ↦₃₂ pad) ∗ ((uss + 16#64) ↦₆₄ ssSize))

/-- Optional 24-byte output `stack_t` buffer at `uoss` (`emp` when `uoss == 0`). -/
def optOldStackTAt (uoss : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  if uoss == 0#64 then emp else (uoss ↦ₛ bs)

/-- Decompose `(addr ↦ₛ sas.toBytes sp)` into the typed 24-byte `stack_t` fields
    (`ss_sp` at `+0`, `ss_flags` at `+8`, zeroed 4-byte padding at `+12`, `ss_size` at `+16`). -/
theorem pointsToBytes_sigAltStack_toBytes (addr : BitVec 64) (sas : SigAltStack) (sp : BitVec 64) :
    (addr ↦ₛ sas.toBytes sp) =
      ((addr ↦₆₄ sas.sp) ∗ ((addr + 8#64) ↦₃₂ sas.flags sp) ∗
       ((addr + 12#64) ↦₃₂ 0#32) ∗ ((addr + 16#64) ↦₆₄ sas.size)) := by
  have hbytes : sas.toBytes sp =
      unpack64 sas.sp ++ (unpack32 (sas.flags sp) ++ (unpack32 0#32 ++ unpack64 sas.size)) := by
    simp [SigAltStack.toBytes, leBytes64, leBytes32, unpack64, unpack32]
  rw [hbytes, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append]
  simp only [unpack64_length, unpack32_length, ← pointsTo64_eq_pointsToBytes,
    ← pointsTo32_eq_pointsToBytes]
  have ha12 : addr + 8#64 + 4#64 = addr + 12#64 := by bv_omega
  have ha16 : addr + 12#64 + 4#64 = addr + 16#64 := by bv_omega
  rw [ha12, ha16]

/-- Convert three 64-bit cells at `uss` (`uss ≠ 0`) into `stackTAt`, splitting `[uss + 8]` into
    32-bit `ss_flags` (`flagsWord.truncate 32`) and 4-byte padding (`flagsWord.extractLsb' 32 32`). -/
theorem stackTAt_eq_of_pointsTo64 (uss ssSp flagsWord ssSize : BitVec 64) (h : uss ≠ 0#64) :
    ((uss ↦₆₄ ssSp) ∗ ((uss + 8#64) ↦₆₄ flagsWord) ∗ ((uss + 16#64) ↦₆₄ ssSize)) =
      stackTAt uss ssSp (flagsWord.truncate 32) (flagsWord.extractLsb' 32 32) ssSize := by
  have hf : (uss == 0#64) = false := beq_false_of_ne h
  dsimp [stackTAt]
  rw [hf, pointsTo64_split32' (uss + 8#64) flagsWord]
  have ha12 : uss + 8#64 + 4#64 = uss + 12#64 := by bv_omega
  rw [ha12]
  simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc]

/-- `SVC #0` rule for `sigaltstack(uss, uoss)` (`X8 = 132`), supporting null `uss` queries,
    `SS_DISABLE` teardown (regardless of `ss_size`), and active stack installation (`ssMode ∈
    {0, SS_ONSTACK}` with `MINSIGSTKSZ ≤ ssSize.toNat`), plus null or non-null `uoss`. -/
theorem SepWP.step_svc_sigaltstack {prog : Program} {target_pc : BitVec 64}
    {s : State} {uss ssSp ssSize uoss : BitVec 64} {ssFlags pad : BitVec 32}
    {oldBs₀ : List (BitVec 8)} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} {pc : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 132#64)
    (huss : s.readReg64 .x0 = uss) (huoss : s.readReg64 .x1 = uoss)
    (hussOk : uss = 0#64 ∨
      (uss.toNat + 24 ≤ 2 ^ 64 ∧
       s.sigAltStack.onSigStack s.sp = false ∧
       ((ssFlags &&& ~~~SS_AUTODISARM) = SS_DISABLE ∨
        (((ssFlags &&& ~~~SS_AUTODISARM) = 0#32 ∨
          (ssFlags &&& ~~~SS_AUTODISARM) = SS_ONSTACK) ∧
         MINSIGSTKSZ ≤ ssSize.toNat))))
    (huossOk : uoss = 0#64 ∨ (uoss.toNat + 24 ≤ 2 ^ 64 ∧ oldBs₀.length = 24))
    (hnext : ∀ m' : Memory,
      let oldBytes := s.sigAltStack.toBytes s.sp
      let ssMode := ssFlags &&& ~~~SS_AUTODISARM
      let s₁ :=
        if uss == 0#64 then s
        else if ssMode == SS_DISABLE then
          s.setSigAltStack { sp := 0#64, size := 0#64, ssFlags }
        else
          s.setSigAltStack { sp := ssSp, size := ssSize, ssFlags }
      SepWP prog target_pc (((s₁.setMem m').writeReg64 .x0 0#64).setPC (pc + 4#64))
        (stackTAt uss ssSp ssFlags pad ssSize ∗
          (optOldStackTAt uoss oldBytes ∗ F)) post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execSigaltstack s := by
      simp [wp_norm, arm64_norm, Reg.x8, *]) :
    SepWP prog target_pc s
      (stackTAt uss ssSp ssFlags pad ssSize ∗ (optOldStackTAt uoss oldBs₀ ∗ F)) post oom := by
  let _ := hx8
  intro R hm
  have huss_mem : s.readReg64 .x0 = 0#64 ∨
      ((s.readReg64 .x0).toNat + 24 ≤ 2 ^ 64 ∧
       s.mem.canRead (s.readReg64 .x0) 24 = true ∧
       s.sigAltStack.onSigStack s.sp = false ∧
       ((s.mem.read32 (s.readReg64 .x0 + 8#64) &&& ~~~SS_AUTODISARM) = SS_DISABLE ∨
        (((s.mem.read32 (s.readReg64 .x0 + 8#64) &&& ~~~SS_AUTODISARM) = 0#32 ∨
          (s.mem.read32 (s.readReg64 .x0 + 8#64) &&& ~~~SS_AUTODISARM) = SS_ONSTACK) ∧
         MINSIGSTKSZ ≤ (s.mem.read64 (s.readReg64 .x0 + 16#64)).toNat))) := by
    by_cases hu0 : uss = 0#64
    · exact Or.inl (huss.trans hu0)
    · rcases hussOk with rfl | ⟨hfit, hon, hmode⟩
      · exact False.elim (hu0 rfl)
      · right
        have hu_f : (uss == 0#64) = false := beq_false_of_ne hu0
        have hm_u : s.mem ⊨ ((uss ↦₆₄ ssSp) ∗ ((uss + 8#64) ↦₃₂ ssFlags) ∗
            ((uss + 12#64) ↦₃₂ pad) ∗ ((uss + 16#64) ↦₆₄ ssSize)) ∗
            (optOldStackTAt uoss oldBs₀ ∗ F ∗ R) := by
          dsimp [stackTAt] at hm; rw [hu_f] at hm; simp only [Bool.false_eq_true, ↓reduceIte] at hm
          ac_nf at hm ⊢
        have hm_fl : s.mem ⊨ ((uss + 8#64) ↦₃₂ ssFlags) ∗ ((uss ↦₆₄ ssSp) ∗
            ((uss + 12#64) ↦₃₂ pad) ∗ ((uss + 16#64) ↦₆₄ ssSize) ∗
            (optOldStackTAt uoss oldBs₀ ∗ F ∗ R)) := by ac_nf at hm_u ⊢
        have hm_sz : s.mem ⊨ ((uss + 16#64) ↦₆₄ ssSize) ∗ ((uss ↦₆₄ ssSp) ∗
            ((uss + 8#64) ↦₃₂ ssFlags) ∗ ((uss + 12#64) ↦₃₂ pad) ∗
            (optOldStackTAt uoss oldBs₀ ∗ F ∗ R)) := by ac_nf at hm_u ⊢
        have hrd_fl : s.mem.read32 (uss + 8#64) = ssFlags :=
          (IsBlock.pointsTo32 (uss + 8#64) ssFlags).read hm_fl
        have hrd_sz : s.mem.read64 (uss + 16#64) = ssSize :=
          (IsBlock.pointsTo64 (uss + 16#64) ssSize).read hm_sz
        have h24 : ((uss ↦₆₄ ssSp) ∗ ((uss + 8#64) ↦₃₂ ssFlags) ∗
            ((uss + 12#64) ↦₃₂ pad) ∗ ((uss + 16#64) ↦₆₄ ssSize)) =
            (uss ↦ₛ (unpack64 ssSp ++ (unpack32 ssFlags ++ (unpack32 pad ++ unpack64 ssSize)))) := by
          rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append]
          simp only [unpack64_length, unpack32_length, ← pointsTo64_eq_pointsToBytes,
            ← pointsTo32_eq_pointsToBytes]
          have ha12 : uss + 8#64 + 4#64 = uss + 12#64 := by bv_omega
          have ha16 : uss + 12#64 + 4#64 = uss + 16#64 := by bv_omega
          rw [ha12, ha16]
        rw [h24] at hm_u
        have hlen24 : (unpack64 ssSp ++ (unpack32 ssFlags ++ (unpack32 pad ++ unpack64 ssSize))).length = 24 := by
          simp only [List.length_append, unpack64_length, unpack32_length]
        have hcr : s.mem.canRead uss 24 = true :=
          hlen24 ▸ (IsBlock.pointsToBytes uss _).canRead (by omega) hm_u
        rw [huss, hrd_fl, hrd_sz]
        exact ⟨hfit, hcr, hon, hmode⟩
  have huoss_mem : s.readReg64 .x1 = 0#64 ∨
      ((s.readReg64 .x1).toNat + 24 ≤ 2 ^ 64 ∧ s.mem.canWrite (s.readReg64 .x1) 24 = true) := by
    by_cases ho0 : uoss = 0#64
    · exact Or.inl (huoss.trans ho0)
    · rcases huossOk with rfl | ⟨hfit, hlen⟩
      · exact False.elim (ho0 rfl)
      · right
        have ho_f : (uoss == 0#64) = false := beq_false_of_ne ho0
        have hm_o : s.mem ⊨ (uoss ↦ₛ oldBs₀) ∗
            (stackTAt uss ssSp ssFlags pad ssSize ∗ F ∗ R) := by
          dsimp [optOldStackTAt] at hm; rw [ho_f] at hm
          simp only [Bool.false_eq_true, ↓reduceIte] at hm; ac_nf at hm ⊢
        have hcw : s.mem.canWrite uoss 24 = true :=
          hlen ▸ (IsBlock.pointsToBytes uoss oldBs₀).canWrite ((IsBlock.pointsToBytes uoss oldBs₀).read hm_o).1 hm_o
        rw [huoss]; exact ⟨hfit, hcw⟩
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  rw [hsvc, execSigaltstack_ok s huss_mem huoss_mem]
  dsimp only
  rw [huss, huoss]
  have hs1_eq :
      (if uss == 0#64 then s
       else if (s.mem.read32 (uss + 8#64) &&& ~~~SS_AUTODISARM) == SS_DISABLE then
         s.setSigAltStack
           { sp := 0#64, size := 0#64,
             ssFlags := s.mem.read32 (uss + 8#64) }
       else
         s.setSigAltStack
           { sp := s.mem.read64 uss, size := s.mem.read64 (uss + 16#64),
             ssFlags := s.mem.read32 (uss + 8#64) }) =
      (if uss == 0#64 then s
       else if (ssFlags &&& ~~~SS_AUTODISARM) == SS_DISABLE then
         s.setSigAltStack
           { sp := 0#64, size := 0#64,
             ssFlags := ssFlags }
       else
         s.setSigAltStack
           { sp := ssSp, size := ssSize,
             ssFlags := ssFlags }) := by
    by_cases hu0 : uss = 0#64
    · simp [hu0]
    · have hu_f : (uss == 0#64) = false := beq_false_of_ne hu0
      simp only [hu_f, Bool.false_eq_true, ↓reduceIte]
      dsimp [stackTAt] at hm; rw [hu_f] at hm; simp only [Bool.false_eq_true, ↓reduceIte] at hm
      have hm0 : s.mem ⊨ (uss ↦₆₄ ssSp) ∗ (((uss + 8#64) ↦₃₂ ssFlags) ∗ ((uss + 12#64) ↦₃₂ pad) ∗
          ((uss + 16#64) ↦₆₄ ssSize) ∗ optOldStackTAt uoss oldBs₀ ∗ F ∗ R) := by ac_nf at hm ⊢
      have hm1 : s.mem ⊨ ((uss + 8#64) ↦₃₂ ssFlags) ∗ ((uss ↦₆₄ ssSp) ∗ ((uss + 12#64) ↦₃₂ pad) ∗
          ((uss + 16#64) ↦₆₄ ssSize) ∗ optOldStackTAt uoss oldBs₀ ∗ F ∗ R) := by ac_nf at hm ⊢
      have hm2 : s.mem ⊨ ((uss + 16#64) ↦₆₄ ssSize) ∗ ((uss ↦₆₄ ssSp) ∗ ((uss + 8#64) ↦₃₂ ssFlags) ∗
          ((uss + 12#64) ↦₃₂ pad) ∗ optOldStackTAt uoss oldBs₀ ∗ F ∗ R) := by ac_nf at hm ⊢
      rw [(IsBlock.pointsTo64 _ _).read hm0, (IsBlock.pointsTo32 _ _).read hm1,
        (IsBlock.pointsTo64 _ _).read hm2]
  rw [hs1_eq]
  have hadv : ∀ st : State, st.pc = pc →
      (st.writeReg64 .x0 0#64).advancePC = (st.writeReg64 .x0 0#64).setPC (pc + 4#64) := by
    intro st hp; cases st; simp [State.writeReg64, State.advancePC, State.setPC, hp]
  let ssMode := ssFlags &&& ~~~SS_AUTODISARM
  let s₁ :=
    if uss == 0#64 then s
    else if ssMode == SS_DISABLE then
      s.setSigAltStack { sp := 0#64, size := 0#64, ssFlags }
    else
      s.setSigAltStack { sp := ssSp, size := ssSize, ssFlags }
  have hs1_mem : s₁.mem = s.mem := by dsimp [s₁]; split <;> (try split) <;> (cases s; rfl)
  have hs1_pc : s₁.pc = pc := by dsimp [s₁]; split <;> (try split) <;> (cases s; exact hpc)
  have hs1_set : s₁.setMem s.mem = s₁ := by dsimp [s₁]; split <;> (try split) <;> (cases s; rfl)
  by_cases ho0 : uoss = 0#64
  · subst ho0; simp only [beq_self_eq_true, ↓reduceIte]
    change reaches_pc prog target_pc ((s₁.writeReg64 .x0 0#64).advancePC) _ _
    rw [hadv s₁ hs1_pc, ← hs1_set]
    apply hnext s.mem R
    change s.mem ⊨ _
    simpa [optOldStackTAt] using hm
  · have ho_f : (uoss == 0#64) = false := beq_false_of_ne ho0
    rcases huossOk with rfl | ⟨_, hlen⟩
    · exact False.elim (ho0 rfl)
    · simp only [ho_f, Bool.false_eq_true, ↓reduceIte]
      change reaches_pc prog target_pc
        (((s₁.setMem (s₁.mem.writeBytes uoss (s.sigAltStack.toBytes s.sp))).writeReg64 .x0 0#64).advancePC) _ _
      rw [hs1_mem]
      let m' := s.mem.writeBytes uoss (s.sigAltStack.toBytes s.sp)
      have hs1m_pc : (s₁.setMem m').pc = pc := by
        dsimp [s₁]; split <;> (try split) <;> (cases s; exact hpc)
      rw [hadv (s₁.setMem m') hs1m_pc]
      apply hnext m' R
      change m' ⊨ _
      dsimp [optOldStackTAt] at hm ⊢; rw [ho_f] at hm ⊢
      simp only [Bool.false_eq_true, ↓reduceIte] at hm ⊢
      have hm_o : s.mem ⊨ (uoss ↦ₛ oldBs₀) ∗
          (stackTAt uss ssSp ssFlags pad ssSize ∗ F ∗ R) := by ac_nf at hm ⊢
      have hlen_eq : oldBs₀.length = (s.sigAltStack.toBytes s.sp).length := by
        rw [hlen]; rfl
      have hm_w := writeBytes_satisfies hlen_eq hm_o
      ac_nf at hm_w ⊢

/-- Optional 32-byte input `struct k_sigaction` at `act` (`emp` when `act == 0`). -/
def kSigActionAt (act handler flags restorer mask : BitVec 64) : SepProp :=
  if act == 0#64 then emp
  else ((act ↦₆₄ handler) ∗ ((act + 8#64) ↦₆₄ flags) ∗
    ((act + 16#64) ↦₆₄ restorer) ∗ ((act + 24#64) ↦₆₄ mask))

/-- Optional 32-byte output `struct k_sigaction` buffer at `oldact` (`emp` when `oldact == 0`). -/
def optOldSigActionAt (oldact : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  if oldact == 0#64 then emp else (oldact ↦ₛ bs)

/-- `SVC #0` rule for `rt_sigaction(signum, act, oldact, 8)` (`X8 = 134`), supporting `SIG_DFL` /
    `SIG_IGN` on any catchable signal and custom user-space handlers on `LINUX_SIGSEGV` /
    `LINUX_SIGBUS`, plus null or non-null `act` / `oldact`. -/
theorem SepWP.step_svc_rt_sigaction_any {prog : Program} {target_pc : BitVec 64}
    {s : State} {signum : BitVec 32} {act handler flags restorer mask oldact : BitVec 64}
    {oldBs₀ : List (BitVec 8)} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} {pc : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 134#64)
    (hsig : s.readReg32 .x0 = signum) (hact : s.readReg64 .x1 = act)
    (hold : s.readReg64 .x2 = oldact) (hsigset : s.readReg64 .x3 = 8#64)
    (hlo : 1 ≤ signum.toNat) (hhi : signum.toNat ≤ 64)
    (hactOk : act = 0#64 ∨ (signum ≠ LINUX_SIGKILL ∧ signum ≠ LINUX_SIGSTOP ∧
      act.toNat + 32 ≤ 2 ^ 64 ∧
      (handler = SIG_DFL ∨ handler = SIG_IGN ∨
       signum = LINUX_SIGSEGV ∨ signum = LINUX_SIGBUS)))
    (holdOk : oldact = 0#64 ∨ (oldact.toNat + 32 ≤ 2 ^ 64 ∧ oldBs₀.length = 32))
    (hnext : ∀ m' : Memory,
      let oldAction := s.getSigAction signum
      let s₁ := if act == 0#64 then s else s.setSigAction signum
        { handler, flags := flags &&& UAPI_SA_FLAGS, restorer, mask := mask &&& ~~~SIG_UNBLOCKABLE_MASK }
      SepWP prog target_pc (((s₁.setMem m').writeReg64 .x0 0#64).setPC (pc + 4#64))
        (kSigActionAt act handler flags restorer mask ∗
          (optOldSigActionAt oldact oldAction.toBytes ∗ F)) post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execRtSigaction s := by
      simp [wp_norm, arm64_norm, Reg.x8, *]) :
    SepWP prog target_pc s
      (kSigActionAt act handler flags restorer mask ∗ (optOldSigActionAt oldact oldBs₀ ∗ F)) post oom := by
  let _ := hx8
  intro R hm
  have hact_mem : s.readReg64 .x1 = 0#64 ∨ (s.readReg32 .x0 ≠ LINUX_SIGKILL ∧
      s.readReg32 .x0 ≠ LINUX_SIGSTOP ∧ (s.readReg64 .x1).toNat + 32 ≤ 2 ^ 64 ∧
      s.mem.canRead (s.readReg64 .x1) 32 = true ∧
      (s.mem.read64 (s.readReg64 .x1) = SIG_DFL ∨ s.mem.read64 (s.readReg64 .x1) = SIG_IGN ∨
       s.readReg32 .x0 = LINUX_SIGSEGV ∨ s.readReg32 .x0 = LINUX_SIGBUS)) := by
    by_cases ha0 : act = 0#64
    · exact Or.inl (hact.trans ha0)
    · rcases hactOk with rfl | ⟨hnk, hns, hfit, hdisp⟩
      · exact False.elim (ha0 rfl)
      · right
        have ha_f : (act == 0#64) = false := beq_false_of_ne ha0
        have hm_a : s.mem ⊨ ((act ↦₆₄ handler) ∗ ((act + 8#64) ↦₆₄ flags) ∗
            ((act + 16#64) ↦₆₄ restorer) ∗ ((act + 24#64) ↦₆₄ mask)) ∗
            (optOldSigActionAt oldact oldBs₀ ∗ F ∗ R) := by
          dsimp [kSigActionAt] at hm; rw [ha_f] at hm; simp only [Bool.false_eq_true, ↓reduceIte] at hm
          ac_nf at hm ⊢
        have hm_h : s.mem ⊨ (act ↦₆₄ handler) ∗ (((act + 8#64) ↦₆₄ flags) ∗
            ((act + 16#64) ↦₆₄ restorer) ∗ ((act + 24#64) ↦₆₄ mask) ∗
            (optOldSigActionAt oldact oldBs₀ ∗ F ∗ R)) := by ac_nf at hm_a ⊢
        have hrd_h : s.mem.read64 act = handler := (IsBlock.pointsTo64 act handler).read hm_h
        have h32 : ((act ↦₆₄ handler) ∗ ((act + 8#64) ↦₆₄ flags) ∗
            ((act + 16#64) ↦₆₄ restorer) ∗ ((act + 24#64) ↦₆₄ mask)) =
            (act ↦ₛ (unpack64 handler ++ (unpack64 flags ++ (unpack64 restorer ++ unpack64 mask)))) := by
          rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append]
          simp only [unpack64_length, ← pointsTo64_eq_pointsToBytes]
          have ha16 : act + 8#64 + 8#64 = act + 16#64 := by bv_omega
          have ha24 : act + 16#64 + 8#64 = act + 24#64 := by bv_omega
          rw [ha16, ha24]
        rw [h32] at hm_a
        have hlen32 : (unpack64 handler ++ (unpack64 flags ++ (unpack64 restorer ++ unpack64 mask))).length = 32 := by
          simp only [List.length_append, unpack64_length]
        have hcr : s.mem.canRead act 32 = true :=
          hlen32 ▸ (IsBlock.pointsToBytes act _).canRead (by omega) hm_a
        rw [hsig, hact, hrd_h]; exact ⟨hnk, hns, hfit, hcr, hdisp⟩
  have hold_mem : s.readReg64 .x2 = 0#64 ∨
      ((s.readReg64 .x2).toNat + 32 ≤ 2 ^ 64 ∧ s.mem.canWrite (s.readReg64 .x2) 32 = true) := by
    by_cases ho0 : oldact = 0#64
    · exact Or.inl (hold.trans ho0)
    · rcases holdOk with rfl | ⟨hfit, hlen⟩
      · exact False.elim (ho0 rfl)
      · right
        have ho_f : (oldact == 0#64) = false := beq_false_of_ne ho0
        have hm_o : s.mem ⊨ (oldact ↦ₛ oldBs₀) ∗
            (kSigActionAt act handler flags restorer mask ∗ F ∗ R) := by
          dsimp [optOldSigActionAt] at hm; rw [ho_f] at hm
          simp only [Bool.false_eq_true, ↓reduceIte] at hm; ac_nf at hm ⊢
        have hcw : s.mem.canWrite oldact 32 = true :=
          hlen ▸ (IsBlock.pointsToBytes oldact oldBs₀).canWrite ((IsBlock.pointsToBytes oldact oldBs₀).read hm_o).1 hm_o
        rw [hold]; exact ⟨hfit, hcw⟩
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  rw [hsvc, execRtSigaction_any_ok s hsigset (hsig ▸ hlo) (hsig ▸ hhi) hact_mem hold_mem]
  dsimp only
  rw [hsig, hact, hold]
  have hs1_eq : (if act == 0#64 then s else s.setSigAction signum
      { handler := s.mem.read64 act, flags := s.mem.read64 (act + 8#64) &&& UAPI_SA_FLAGS,
        restorer := s.mem.read64 (act + 16#64),
        mask := s.mem.read64 (act + 24#64) &&& ~~~SIG_UNBLOCKABLE_MASK }) =
      (if act == 0#64 then s else s.setSigAction signum
        { handler, flags := flags &&& UAPI_SA_FLAGS, restorer, mask := mask &&& ~~~SIG_UNBLOCKABLE_MASK }) := by
    by_cases ha0 : act = 0#64
    · simp [ha0]
    · have ha_f : (act == 0#64) = false := beq_false_of_ne ha0
      simp only [ha_f, Bool.false_eq_true, ↓reduceIte]
      dsimp [kSigActionAt] at hm; rw [ha_f] at hm; simp only [Bool.false_eq_true, ↓reduceIte] at hm
      have hm0 : s.mem ⊨ (act ↦₆₄ handler) ∗ (((act + 8#64) ↦₆₄ flags) ∗ ((act + 16#64) ↦₆₄ restorer) ∗
          ((act + 24#64) ↦₆₄ mask) ∗ optOldSigActionAt oldact oldBs₀ ∗ F ∗ R) := by ac_nf at hm ⊢
      have hm1 : s.mem ⊨ ((act + 8#64) ↦₆₄ flags) ∗ ((act ↦₆₄ handler) ∗ ((act + 16#64) ↦₆₄ restorer) ∗
          ((act + 24#64) ↦₆₄ mask) ∗ optOldSigActionAt oldact oldBs₀ ∗ F ∗ R) := by ac_nf at hm ⊢
      have hm2 : s.mem ⊨ ((act + 16#64) ↦₆₄ restorer) ∗ ((act ↦₆₄ handler) ∗ ((act + 8#64) ↦₆₄ flags) ∗
          ((act + 24#64) ↦₆₄ mask) ∗ optOldSigActionAt oldact oldBs₀ ∗ F ∗ R) := by ac_nf at hm ⊢
      have hm3 : s.mem ⊨ ((act + 24#64) ↦₆₄ mask) ∗ ((act ↦₆₄ handler) ∗ ((act + 8#64) ↦₆₄ flags) ∗
          ((act + 16#64) ↦₆₄ restorer) ∗ optOldSigActionAt oldact oldBs₀ ∗ F ∗ R) := by ac_nf at hm ⊢
      rw [(IsBlock.pointsTo64 _ _).read hm0, (IsBlock.pointsTo64 _ _).read hm1,
        (IsBlock.pointsTo64 _ _).read hm2, (IsBlock.pointsTo64 _ _).read hm3]
  rw [hs1_eq]
  have hadv : ∀ st : State, st.pc = pc →
      (st.writeReg64 .x0 0#64).advancePC = (st.writeReg64 .x0 0#64).setPC (pc + 4#64) := by
    intro st hp; cases st; simp [State.writeReg64, State.advancePC, State.setPC, hp]
  let s₁ := if act == 0#64 then s else s.setSigAction signum
    { handler, flags := flags &&& UAPI_SA_FLAGS, restorer, mask := mask &&& ~~~SIG_UNBLOCKABLE_MASK }
  have hs1_mem : s₁.mem = s.mem := by dsimp [s₁]; split <;> (cases s; rfl)
  have hs1_pc : s₁.pc = pc := by dsimp [s₁]; split <;> (cases s; exact hpc)
  have hs1_set : s₁.setMem s.mem = s₁ := by dsimp [s₁]; split <;> (cases s; rfl)
  by_cases ho0 : oldact = 0#64
  · subst ho0; simp only [beq_self_eq_true, ↓reduceIte]
    change reaches_pc prog target_pc ((s₁.writeReg64 .x0 0#64).advancePC) _ _
    rw [hadv s₁ hs1_pc, ← hs1_set]
    apply hnext s.mem R
    change s.mem ⊨ _
    simpa [optOldSigActionAt] using hm
  · have ho_f : (oldact == 0#64) = false := beq_false_of_ne ho0
    rcases holdOk with rfl | ⟨_, hlen⟩
    · exact False.elim (ho0 rfl)
    · simp only [ho_f, Bool.false_eq_true, ↓reduceIte]
      change reaches_pc prog target_pc
        (((s₁.setMem (s₁.mem.writeBytes oldact (s.getSigAction signum).toBytes)).writeReg64 .x0 0#64).advancePC) _ _
      rw [hs1_mem]
      let m' := s.mem.writeBytes oldact (s.getSigAction signum).toBytes
      have hs1m_pc : (s₁.setMem m').pc = pc := by dsimp [s₁]; split <;> (cases s; exact hpc)
      rw [hadv (s₁.setMem m') hs1m_pc]
      apply hnext m' R
      change m' ⊨ _
      dsimp [optOldSigActionAt] at hm ⊢; rw [ho_f] at hm ⊢
      simp only [Bool.false_eq_true, ↓reduceIte] at hm ⊢
      have hm_o : s.mem ⊨ (oldact ↦ₛ oldBs₀) ∗
          (kSigActionAt act handler flags restorer mask ∗ F ∗ R) := by ac_nf at hm ⊢
      have hlen_eq : oldBs₀.length = (s.getSigAction signum).toBytes.length := by
        rw [hlen]; rfl
      have hm_w := writeBytes_satisfies hlen_eq hm_o
      ac_nf at hm_w ⊢

/-- `SVC #0` rule for `rt_sigaction(signum, act, oldact, 8)` (`X8 = 134`), supporting both null and
    non-null `act` / `oldact`. -/
theorem SepWP.step_svc_rt_sigaction {prog : Program} {target_pc : BitVec 64}
    {s : State} {signum : BitVec 32} {act handler flags restorer mask oldact : BitVec 64}
    {oldBs₀ : List (BitVec 8)} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} {pc : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 134#64)
    (hsig : s.readReg32 .x0 = signum) (hact : s.readReg64 .x1 = act)
    (hold : s.readReg64 .x2 = oldact) (hsigset : s.readReg64 .x3 = 8#64)
    (hlo : 1 ≤ signum.toNat) (hhi : signum.toNat ≤ 64)
    (hactOk : act = 0#64 ∨ (signum ≠ LINUX_SIGKILL ∧ signum ≠ LINUX_SIGSTOP ∧
      act.toNat + 32 ≤ 2 ^ 64 ∧ (handler = SIG_DFL ∨ handler = SIG_IGN)))
    (holdOk : oldact = 0#64 ∨ (oldact.toNat + 32 ≤ 2 ^ 64 ∧ oldBs₀.length = 32))
    (hnext : ∀ m' : Memory,
      let oldAction := s.getSigAction signum
      let s₁ := if act == 0#64 then s else s.setSigAction signum
        { handler, flags := flags &&& UAPI_SA_FLAGS, restorer, mask := mask &&& ~~~SIG_UNBLOCKABLE_MASK }
      SepWP prog target_pc (((s₁.setMem m').writeReg64 .x0 0#64).setPC (pc + 4#64))
        (kSigActionAt act handler flags restorer mask ∗
          (optOldSigActionAt oldact oldAction.toBytes ∗ F)) post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execRtSigaction s := by
      simp [wp_norm, arm64_norm, Reg.x8, *]) :
    SepWP prog target_pc s
      (kSigActionAt act handler flags restorer mask ∗ (optOldSigActionAt oldact oldBs₀ ∗ F)) post oom :=
  SepWP.step_svc_rt_sigaction_any hpc hrun hfetch hx8 hsig hact hold hsigset hlo hhi
    (hactOk.imp id fun ⟨hk, hs, hf, hd⟩ => ⟨hk, hs, hf, hd.imp id Or.inl⟩) holdOk hnext hsvc

/-- `SVC #0` rule for `exit_group(status)` (`X8 = 94`) under `Program.pureMem`: terminates in one
    step with `ProcessOutcome.ofState (s.readReg64 .x0) s`. -/
theorem step_exit_group_exitsWith {s : State} {pc : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = 94#64)
    (hfetch : Program.pureMem.fetchMem s.mem pc = some (.system false 0#16)) :
    Process.ProcessExitsWith Program.pureMem s (Process.ProcessOutcome.ofState (s.readReg64 .x0) s) := by
  have hstep : Step Program.pureMem s (Program.pureMem.evalInst (.system false 0#16) s) :=
    Step.exec hrun (hpc.symm ▸ hfetch)
  have hev : Program.pureMem.evalInst (.system false 0#16) s = s.setStatus (.Exited (s.readReg64 .x0)) := by
    simp [wp_norm, arm64_norm, hx8]
  rw [hev] at hstep
  refine ⟨s.setStatus (.Exited (s.readReg64 .x0)), Steps.step hstep (Steps.refl _), Or.inl ⟨s.readReg64 .x0, ?_, ?_⟩⟩
  · cases s; rfl
  · cases s; rfl


end ProofLib
