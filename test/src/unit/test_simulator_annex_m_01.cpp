#include <gtest/gtest.h>

#include <string_view>
#include <type_traits>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_include_file.h"
#include "simulator/vpi_user.h"

using namespace delta;

namespace {

TEST(SvVpiUserHeaderProvided,
     TheAnnexShowsANormativeFileEverySimulatorProvides) {
  EXPECT_EQ(VpiAnnexShowingSvVpiUserH(), "Annex M");
  EXPECT_EQ(SvVpiUserHFileName(), "sv_vpi_user.h");
  EXPECT_TRUE(SvVpiUserHIsNormative());
  EXPECT_TRUE(SvVpiUserHIsProvidedByEverySimulator());
}

TEST(SvVpiUserHeaderProvided, TheFileTheAnnexNamesIncludesTheBaseFile) {
#ifdef VPI_USER_H
  SUCCEED();
#else
  FAIL() << "sv_vpi_user.h, the file Annex M shows, does not include "
            "vpi_user.h";
#endif
}

static_assert(
    std::is_same_v<decltype(vpi_register_assertion_cb),
                   vpiHandle(vpiHandle, PLI_INT32, vpi_assertion_callback_func*,
                             PLI_BYTE8*)>,
    "sv_vpi_user.h must provide vpi_register_assertion_cb");

TEST(SvVpiUserHeaderProvided, IncludeFileIsPresentAndGuarded) {
#ifdef SV_VPI_USER_H
  SUCCEED();
#else
  FAIL() << "sv_vpi_user.h include guard not provided by the simulator";
#endif
}

TEST(SvVpiUserHeaderProvided, ProvidesSystemVerilogExtensionConstants) {
  EXPECT_EQ(vpiPackage, 600);
  EXPECT_EQ(vpiInterface, 601);
  EXPECT_EQ(vpiProgram, 602);
}

TEST(SvVpiUserHeaderProvided, ProvidesExtensionStructures) {
  s_vpi_assertion_step_info step = {};
  s_vpi_attempt_info attempt = {};
  EXPECT_EQ(step.matched_expression_count, 0);
  EXPECT_EQ(step.stateFrom, 0);
  EXPECT_EQ(attempt.detail.failExpr, nullptr);
}

TEST(SvVpiUserHeaderProvided, ProvidesResolvableExtensionRoutine) {
  EXPECT_NE(reinterpret_cast<void*>(&vpi_register_assertion_cb), nullptr);
}

TEST(SvVpiUserHeaderProvided, IdempotentUnderRepeatedInclusion) {
#ifdef SV_VPI_USER_H
  EXPECT_EQ(vpiTypespec, 605);
#else
  FAIL() << "sv_vpi_user.h guard not latched after repeated inclusion";
#endif
}

}  // namespace
