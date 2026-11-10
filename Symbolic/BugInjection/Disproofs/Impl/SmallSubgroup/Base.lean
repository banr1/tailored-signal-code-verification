/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module
public import GeneratedLean.BugInjectionMutantImage
public import Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlaced
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.MutantLinkData
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.MutantLink
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseFull
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseScalarsHooks
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseTail
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseCheck0
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseCheck1
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseCheck2
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseCheck3
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseCheck4
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseCheck5
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseCheck6
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseCheck7
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseCheck8
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseCheck9
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseCheck10
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseCheck11
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseCheck12
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseCheck13
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseCheck14
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.BaseCheck15
@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.Base
open CryptoVerification.BugInjection (mutantCliElfImage)
open Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlaced (ElfFullValidPlaced elfFullValidPlaced_of_depth4)
open Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.MutantLink (mutantMpl mutantMmpl)
theorem ssSpec_valid : ElfFullValidPlaced mutantMpl mutantMmpl mutantCliElfImage BaseFull.ssSpec :=
  elfFullValidPlaced_of_depth4 MutantLink.mutantMmpl_linkedIn.2 BaseScalarsHooks.base_scalars BaseScalarsHooks.base_hooks BaseTail.base_depth4
    BaseCheck0.base_sub0 BaseCheck1.base_sub1 BaseCheck2.base_sub2 BaseCheck3.base_sub3 BaseCheck4.base_sub4
    BaseCheck5.base_sub5 BaseCheck6.base_sub6 BaseCheck7.base_sub7 BaseCheck8.base_sub8 BaseCheck9.base_sub9 BaseCheck10.base_sub10
    BaseCheck11.base_sub11 BaseCheck12.base_sub12 BaseCheck13.base_sub13 BaseCheck14.base_sub14 BaseCheck15.base_sub15 rfl
end Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.Base
