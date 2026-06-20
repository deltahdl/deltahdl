#include <gtest/gtest.h>

#include <type_traits>

// §K.1 General makes a single normative claim: vpi_user.h is a normative
// include file that every SystemVerilog simulator shall provide. The simulator
// stage carries that obligation through the VPI access header pulled in below
// (it in turn includes simulator/vpi.h, which declares the VPI routine set).
// These tests observe that the header is genuinely provided: includable, guard-
// protected, supplying the canonical VPI types and resolvable access routines.
// The exhaustive contents (constant values, struct layouts) belong to §K.2 and
// are exercised by its own canonical test; §K.1's lane is provision itself.
#include "simulator/sv_vpi_user.h"

// Deliberately include the provided header a second time. A normative include
// file must be safe to pull in more than once; the production
// multiple-inclusion guard in sv_vpi_user.h is what makes this translation unit
// compile despite the repeat. Compilation succeeding is itself the observation
// for the edge case below.
#include "simulator/sv_vpi_user.h"

namespace {

// Compile-time provision lock: the supplied header must declare the core VPI
// access routines with their canonical PLI-typed signatures. Naming the
// function types via decltype neither calls nor odr-uses them, so this checks
// declaration provision purely at compile time.
static_assert(std::is_same_v<decltype(vpi_register_cb), vpiHandle(s_cb_data*)>,
              "vpi_user.h must provide vpi_register_cb");
static_assert(std::is_same_v<decltype(vpi_get), int(int, vpiHandle)>,
              "vpi_user.h must provide vpi_get");
static_assert(std::is_same_v<decltype(vpi_iterate), vpiHandle(int, vpiHandle)>,
              "vpi_user.h must provide vpi_iterate");
static_assert(std::is_same_v<decltype(vpi_scan), vpiHandle(vpiHandle)>,
              "vpi_user.h must provide vpi_scan");
static_assert(
    std::is_same_v<decltype(vpi_get_value), void(vpiHandle, s_vpi_value*)>,
    "vpi_user.h must provide vpi_get_value");
static_assert(std::is_same_v<decltype(vpi_handle_by_name),
                             vpiHandle(const char*, vpiHandle)>,
              "vpi_user.h must provide vpi_handle_by_name");

TEST(VpiUserHeaderProvided, IncludeFileIsPresentAndGuarded) {
  // The normative include file was reachable to compile this translation unit,
  // and provides its multiple-inclusion guard. A defined SV_VPI_USER_H is the
  // observable trace that the simulator-provided vpi_user.h was included.
#ifdef SV_VPI_USER_H
  SUCCEED();
#else
  FAIL() << "vpi_user.h include guard not provided by the simulator";
#endif
}

TEST(VpiUserHeaderProvided, ProvidesCanonicalVpiTypes) {
  // §K.1: the include file is the carrier of the VPI access interface, so the
  // canonical handle type and the core value/time/callback structures must be
  // usable once it is included. The handle is the opaque pointer every routine
  // trades in.
  EXPECT_TRUE(std::is_pointer_v<vpiHandle>);

  s_vpi_value value = {};
  s_vpi_time time = {};
  s_cb_data cb = {};
  vpiHandle handle = nullptr;
  EXPECT_EQ(value.format, 0);
  EXPECT_EQ(time.type, 0);
  EXPECT_EQ(cb.reason, 0);
  EXPECT_EQ(handle, nullptr);
}

TEST(VpiUserHeaderProvided, ProvidesResolvableAccessRoutines) {
  // Provision is more than a declaration: the routines the header promises are
  // backed by the simulator and resolve at link time. Taking their addresses
  // odr-uses them, so a non-null pointer for each confirms the simulator
  // genuinely supplies the interface the include file advertises.
  EXPECT_NE(reinterpret_cast<void*>(&vpi_register_cb), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_get), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_iterate), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_scan), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_get_value), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_put_value), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_handle_by_name), nullptr);
  EXPECT_NE(reinterpret_cast<void*>(&vpi_printf), nullptr);
}

TEST(VpiUserHeaderProvided, IdempotentUnderRepeatedInclusion) {
  // Edge case: a normative include file must tolerate being included more than
  // once. The header is pulled in twice at the top of this file; the production
  // guard suppresses the second expansion, so there is no redefinition and the
  // unit still compiles. With the guard latched, a representative interface
  // symbol remains defined exactly once and usable, confirming the repeated
  // inclusion collapsed to a single effective one rather than redefining.
#ifdef SV_VPI_USER_H
  s_vpi_value value = {};
  value.format = 0;
  EXPECT_EQ(value.format, 0);
#else
  FAIL() << "vpi_user.h guard not latched after repeated inclusion";
#endif
}

}  // namespace
