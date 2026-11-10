// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Rust and inline-assembly example functions and classic algorithms compiled to AArch64 and exported to Lean 4.

#![no_std]
#![deny(unsafe_op_in_unsafe_fn)]

extern crate alloc;

#[cfg(feature = "panic-handler")]
#[panic_handler]
fn panic(_info: &core::panic::PanicInfo<'_>) -> ! {
    syscalls::sys::exit_group(101)
}

#[cfg(feature = "panic-handler")]
#[unsafe(no_mangle)]
extern "C" fn rust_eh_personality() {}

pub mod algorithms;
pub mod arithmetic_and_branches;
pub mod automation_survey;
pub mod compositional_calls;
pub mod functional_correctness;
pub mod functions;
pub mod machine_code_and_loops;
pub mod memory_and_stack;
pub mod sep_wp_examples;
pub mod simd_and_atomics;
pub mod syscalls;
