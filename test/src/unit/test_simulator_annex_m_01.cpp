#include <gtest/gtest.h>

#include <type_traits>

// §M.1 General makes a single normative claim: sv_vpi_user.h is a normative
// include file that every SystemVerilog simulator shall provide. Where §K.1
// covers provision of the base IEEE 1364 vpi_user.h interface, §M.1's lane is
// the SystemVerilog VPI *extensions* — the constants, structures, and routine
// declarations that sv_vpi_user.h layers on top of that base. The simulator
// stage carries the obligation through the production header pulled in below.
// These tests observe that the SV-extension header is genuinely provided:
// includable, guard-protected, supplying its extension constants/structures and
// a resolvable extension routine. The exhaustive contents (every constant value
// and struct layout of the listing) belong to §M.2 and are exercised by its own
// canonical test; §M.1's lane is provision of the file itself.
#include "simulator/sv_vpi_user.h"

// Deliberately include the provided header a second time. A normative include
// file must be safe to pull in more than once; the production multiple-inclusion
// guard in sv_vpi_user.h is what makes this translation unit compile despite the
// repeat. Compilation succeeding is itself the observation for the edge case
// below.
#include "simulator/sv_vpi_user.h"

namespace {

// Compile-time provision lock: the supplied header must declare the
// SystemVerilog VPI extension routine with its canonical PLI-typed signature.
// vpi_register_assertion_cb is declared in sv_vpi_user.h itself (not in the base
// vpi_user.h), so it is the symbol that distinguishes provision of the SV
// extensions from provision of the base interface. Naming the function type via
// decltype neither calls nor odr-uses it, so this checks declaration provision
// purely at compile time.
static_assert(
    std::is_same_v<decltype(vpi_register_assertion_cb),
                   vpiHandle(vpiHandle, PLI_INT32, vpi_assertion_callback_func,
                             PLI_BYTE8*)>,
    "sv_vpi_user.h must provide vpi_register_assertion_cb");

TEST(SvVpiUserHeaderProvided, IncludeFileIsPresentAndGuarded) {
  // The normative include file was reachable to compile this translation unit,
  // and provides its multiple-inclusion guard. A defined SV_VPI_USER_H is the
  // observable trace that the simulator-provided sv_vpi_user.h was included.
#ifdef SV_VPI_USER_H
  SUCCEED();
#else
  FAIL() << "sv_vpi_user.h include guard not provided by the simulator";
#endif
}

TEST(SvVpiUserHeaderProvided, ProvidesSystemVerilogExtensionConstants) {
  // §M.1: the include file is the carrier of the SystemVerilog VPI extensions,
  // so its extension object-type constants must be usable once it is included.
  // These names exist only because the production header layered them on top of
  // the base interface; their availability is the trace of SV-extension
  // provision. (The specific values are §M.2's concern; here we only observe
  // that the symbols are supplied.)
  EXPECT_EQ(vpiPackage, 600);
  EXPECT_EQ(vpiInterface, 601);
  EXPECT_EQ(vpiProgram, 602);
}

TEST(SvVpiUserHeaderProvided, ProvidesExtensionStructures) {
  // The extension structures the header introduces for the assertion VPI must be
  // usable types once the header is included. Instantiating them and touching a
  // member confirms the simulator genuinely supplies the layouts the include
  // file advertises.
  s_vpi_assertion_step_info step = {};
  s_vpi_attempt_info attempt = {};
  EXPECT_EQ(step.matched_expression_count, 0);
  EXPECT_EQ(step.state_from, 0);
  EXPECT_EQ(attempt.detail.fail_expr, nullptr);
}

TEST(SvVpiUserHeaderProvided, ProvidesResolvableExtensionRoutine) {
  // Provision is more than a declaration: the SV extension routine the header
  // promises is backed by the simulator and resolves at link time. Taking its
  // address odr-uses it, so a non-null pointer confirms the simulator genuinely
  // supplies the extension interface the include file advertises.
  EXPECT_NE(reinterpret_cast<void*>(&vpi_register_assertion_cb), nullptr);
}

TEST(SvVpiUserHeaderProvided, IdempotentUnderRepeatedInclusion) {
  // Edge case: a normative include file must tolerate being included more than
  // once. The header is pulled in twice at the top of this file; the production
  // guard suppresses the second expansion, so there is no redefinition and the
  // unit still compiles. With the guard latched, a representative extension
  // constant remains defined exactly once and usable, confirming the repeated
  // inclusion collapsed to a single effective one rather than redefining.
#ifdef SV_VPI_USER_H
  EXPECT_EQ(vpiTypespec, 605);
#else
  FAIL() << "sv_vpi_user.h guard not latched after repeated inclusion";
#endif
}

}  // namespace
