/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.Pure
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.Decode
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.Hit
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.RoData
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.Top
import ProofLib.SepLogic.WPp

/-!
# `signal_session::io::read_file` Call Site and Top-Level `dirGet_ok_of_loads`

Isolates `read_file` symbol and contract references for `Dir::get`, discharging `PathIoContract`
at `+0x14c` → `+0x150` under `FsInv` and deriving `dirGet_ok_of_loads` from `Obj.Loads`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Get.Helpers

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession.Cli

ls_attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
ls_attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem frozenLoaded_of_mem_eq {img : Obj.Image} {s1 s2 : State}
    (h : img.FrozenLoaded s1) (hm : s1.mem = s2.mem) : img.FrozenLoaded s2 :=
  h.of_keepsFrozen (hm ▸ Memory.KeepsFrozen.refl s1.mem)

/-- Step across `bl signal_session::io::read_file` (`+0x14c` → `+0x150`), recovering
    `s.fs.files = s0.fs.files` from `FsInv s0.fs.files s0.trace s` (`evs := []`) and carrying
    `FsInv` across the call via `hFs`. -/
theorem step_read_file_call
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {readStk : Nat}
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr readFileName)
      (readFileSpec rd pathOk A img readStk))
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext)) :
    PathIoContract img A ext rd pathOk readStk := by
  have hAt : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName +
        bv% (ls_rel% "<libsignal_cli::stores::Dir>::get" "libsignal_cli_io::read_file"))
      (readFileSpec rd pathOk A img readStk) := by
    rw [fnAddr_add_rel dirGetName readFileName (by rw [dirGet_fnOff, readFile_fnOff])]
    exact hRead
  have _ := hFs
  have hfn : libsignalSessionCode.fnOff dirGetName =
      ls_off% "<libsignal_cli::stores::Dir>::get" := dirGet_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode dirGetBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_cli::stores::Dir>::get")) 332 4
  dsimp only [tripleRatchetProgAtExt] at hAt
  clear hfn hRead hFs
  intro s0 s pathPtr pth F Q Qp prog fnStart hfz hsym hpc hrun hsp hinv htr
    hx0 hx1 hx8 hlt hpOk hQp_false hnext
  dsimp only [prog, fnStart] at hpc hnext ⊢
  clear prog fnStart
  have hfiles : s.fs.files = s0.fs.files :=
    hinv.files_eq (evs := []) (by simp [htr]) NoFsEv.nil
  generalize hentry_raw :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr dirGetName = fnStart at *
  generalize hprog_raw :
    libsignalSessionCode.rebase img.base (Rust.withPanics ext) = prog at *
  have he : FrozenEq (prog.fnAddr dirGetName) fnStart := ⟨hentry_raw⟩
  have hp : FrozenEq (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) prog := ⟨hprog_raw⟩
  clear hentry_raw hprog_raw
  examples_hide_fetches
  refine SepWPp.seq_frozen
    (mid := fnStart + bv% (ls_rel% "<libsignal_cli::stores::Dir>::get" "libsignal_cli_io::read_file"))
    (Φ := fun m => img.FrozenLoaded { s with mem := m })
    (fun m m' hf hkf => Obj.Image.FrozenLoaded.of_keepsFrozen
      (s := { s with mem := m }) (s' := { s with mem := m' }) hf hkf)
    hfz ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hfz1
  refine SepWPp.call_inImage_frame (x := ReadFileGhost.mk pathPtr pth s.sp)
    (T := (pathPtr ↦ₛ pth) ∗ memRegion s.sp 24 ∗ stackAt s.sp readStk ∗ A.pool)
    (F := F)
    hAt (frozenLoaded_of_mem_eq hfz1 (by simp only [wp_norm]))
    (by simp only [wp_norm, *]) (by wp_norm_lhs)
    (by simp only [wp_norm, *])
    (by simpa only [arm64_norm] using hsp)
    (by wp_norm_lhs)
    (by dsimp only [readFileSpec, Spec.inImage]; simp only [wp_norm]; rfl)
    (by refine ⟨by simp only [wp_norm, arm64_norm, *],
                by simp only [wp_norm, arm64_norm, *],
                by simp only [wp_norm, arm64_norm, *],
                hlt, hpOk⟩)
    (by simp only [wp_norm])
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun sf _ => hQp_false _ sf F (by simp only [wp_norm, arm64_norm, *]))
    (fun sf hpc_f hrun_f hsp_f hcs hfz_f hsym_f => ?_)
  have hcs' : CalleeSavedPreserved s sf := ⟨
    by simpa only [wp_norm] using hcs.1,
    by simpa only [wp_norm] using hcs.2.1,
    by simpa only [wp_norm] using hcs.2.2.1,
    by simpa only [wp_norm] using hcs.2.2.2.1,
    by simpa only [wp_norm] using hcs.2.2.2.2.1,
    by simpa only [wp_norm] using hcs.2.2.2.2.2.1,
    by simpa only [wp_norm] using hcs.2.2.2.2.2.2.1,
    by simpa only [wp_norm] using hcs.2.2.2.2.2.2.2.1,
    by simpa only [wp_norm] using hcs.2.2.2.2.2.2.2.2.1,
    by simpa only [wp_norm] using hcs.2.2.2.2.2.2.2.2.2.1,
    by simpa only [wp_norm] using hcs.2.2.2.2.2.2.2.2.2.2.1,
    by simpa only [calleeSavedVRegs, wp_norm] using hcs.2.2.2.2.2.2.2.2.2.2.2⟩
  have hsp_f' : sf.sp = s.sp := by rw [hsp_f]; simp only [wp_norm]
  rcases he with ⟨rfl⟩; rcases hp with ⟨rfl⟩
  dsimp only [readFileSpec]
  have hh := hnext sf hpc_f hrun_f hsp_f' hcs' hfz_f hsym_f
  simpa [allocFailedIn, wp_norm, arm64_norm, hfiles, htr, sepExists_sepConj_left, sepConj_assoc] using hh

end CryptoVerification.SignalSession.Cli.Get.Helpers

namespace CryptoVerification.SignalSession.Cli.Get

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession.Cli.Get.Helpers

/-- `Dir::get` satisfies `dirGetSpec rd pathOk A img stk` at any 4 KiB-aligned image base under
`Obj.Loads libsignalSessionImage img`. -/
theorem dirGet_ok_of_loads {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {pathStk readStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (hRO : HookSat ext memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpec)
    (hBcmp : HookSat ext cliBcmpName cliBcmpSpec)
    (hPath : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pathName)
      (pathSpec A img pathStk))
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr readFileName)
      (readFileSpec rd pathOk A img readStk))
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hstk : 0x70 + max (max pathStk readStk) extHookStack ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64)
    (himg : Obj.Loads libsignalSessionImage img)
    (hpathLen : ∀ p, pathOk p → p.length < 2 ^ 32) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName)
      (dirGetSpec rd pathOk A img stk) :=
  dirGet_ok_of_ioCall hC hRO hBcmp hPath (step_read_file_call hRead hFs) hFs hstk hb
    (dirGetRoData_of_loads himg) hpathLen

/-- `Dir::get` satisfies `dirGetSpec rd pathOk A img stk` from `MemcpyROOkExtX img ext` and `Obj.Loads`. -/
theorem dirGet_ok_of_loads_roX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {pathStk readStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (hRO : SpqrV1.Alloc.MemcpyROOkExtX img ext)
    (hBcmp : HookSat ext cliBcmpName cliBcmpSpec)
    (hPath : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pathName)
      (pathSpec A img pathStk))
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr readFileName)
      (readFileSpec rd pathOk A img readStk))
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hstk : 0x70 + max (max pathStk readStk) extHookStack ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64)
    (himg : Obj.Loads libsignalSessionImage img)
    (hpathLen : ∀ p, pathOk p → p.length < 2 ^ 32) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName)
      (dirGetSpec rd pathOk A img stk) :=
  dirGet_ok_of_ioCall_roX hC hRO hBcmp hPath (step_read_file_call hRead hFs) hFs hstk hb
    (dirGetRoData_of_loads himg) hpathLen

/-- `Dir::get` satisfies `dirGetSpec rd pathOk A img stk` from a stacked read-only `memcpy` contract and `Obj.Loads`. -/
theorem dirGet_ok_of_loads_withStack {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {pathStk readStk stk roStk : Nat}
    (hC : AllocContractsX img A ext)
    (hRO : HookSat ext memcpyName (SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack roStk))
    (hBcmp : HookSat ext cliBcmpName cliBcmpSpec)
    (hPath : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pathName)
      (pathSpec A img pathStk))
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr readFileName)
      (readFileSpec rd pathOk A img readStk))
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hstk : 0x70 + max (max pathStk readStk) extHookStack ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64)
    (himg : Obj.Loads libsignalSessionImage img)
    (hpathLen : ∀ p, pathOk p → p.length < 2 ^ 32)
    (hro : roStk ≤ extHookStack := by decide) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName)
      (dirGetSpec rd pathOk A img stk) :=
  dirGet_ok_of_ioCall_withStack hC hRO hBcmp hPath (step_read_file_call hRead hFs) hFs hstk hb
    (dirGetRoData_of_loads himg) hpathLen hro

end CryptoVerification.SignalSession.Cli.Get
