/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlacedCore
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseData
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseLines0
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseLines1
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseLines2
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseLines3
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseLines4
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseLines5
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseLines6
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseLines7
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseLines8
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseLines9
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseLines10
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseLines11
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseLines12
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseLines13
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseLines14
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseLines15

/-! Complete pre-elaborated `ElfFullSpecPlaced` (`ssSpec`) for `Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup` (Rule 2: image-free). -/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseFull

open Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlacedCore (ElfFullSpecPlaced mkDepth3)
open Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseData (baseHooks)
open Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseLines0 (sub0)
open Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseLines1 (sub1)
open Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseLines2 (sub2)
open Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseLines3 (sub3)
open Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseLines4 (sub4)
open Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseLines5 (sub5)
open Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseLines6 (sub6)
open Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseLines7 (sub7)
open Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseLines8 (sub8)
open Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseLines9 (sub9)
open Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseLines10 (sub10)
open Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseLines11 (sub11)
open Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseLines12 (sub12)
open Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseLines13 (sub13)
open Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseLines14 (sub14)
open Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseLines15 (sub15)

def ssSpec : ElfFullSpecPlaced :=
  { entry := 0x49c010#64 -- layout-bypass: concrete-mutant-trace-checkpoint
    phdrVaddr := 0x3ff040#64 -- layout-bypass: concrete-mutant-trace-checkpoint
    phnum := 11
    brkStart := 0x4a4000#64 -- layout-bypass: concrete-mutant-trace-checkpoint
    tokStorageAddr := 0x49a038#64 -- layout-bypass: concrete-mutant-trace-checkpoint
    tokOnceAddr := 0x49a040#64 -- layout-bypass: concrete-mutant-trace-checkpoint
    callocAddr := 0x49e418#64 -- layout-bypass: concrete-mutant-trace-checkpoint
    callocSentinel := 0x49e419#64 -- layout-bypass: concrete-mutant-trace-checkpoint
    mallocAddr := 0x49e4fc#64 -- layout-bypass: concrete-mutant-trace-checkpoint
    mallocSentinel := 0x49e4fd#64 -- layout-bypass: concrete-mutant-trace-checkpoint
    freeAddr := 0x49e4f8#64 -- layout-bypass: concrete-mutant-trace-checkpoint
    freeSentinel := 0x49e4f9#64 -- layout-bypass: concrete-mutant-trace-checkpoint
    hooks := baseHooks
    baseLines := mkDepth3
      (.branch sub0 sub8) (.branch sub1 sub9) (.branch sub2 sub10) (.branch sub3 sub11)
      (.branch sub4 sub12) (.branch sub5 sub13) (.branch sub6 sub14) (.branch sub7 sub15) }

end Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseFull
