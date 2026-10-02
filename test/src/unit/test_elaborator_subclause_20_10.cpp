#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(SeveritySystemTaskElab, FatalFinishNumberInRangeAccepted) {
  for (int fn = 0; fn <= 2; ++fn) {
    ElabFixture ef;
    auto src = "module m; $fatal(" + std::to_string(fn) + "); endmodule\n";
    auto* design = Elaborate(src, ef);
    ASSERT_NE(design, nullptr);
    // The $fatal's own report (§20.10.1) is the one error: the
    // finish_number is accepted.
    EXPECT_EQ(ef.diag.ErrorCount(), 1u)
        << "finish_number " << fn << " must be accepted";
  }
}

TEST(SeveritySystemTaskElab, FatalFinishNumberOutOfRangeRejected) {
  ElabFixture ef;
  auto* design = Elaborate(
      "module m;\n"
      "  $fatal(5);\n"
      "endmodule\n",
      ef);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(ef.diag.Diagnostics(),
                            "finish_number must be 0, 1, or 2", 2, "20.10"));
}

}  // namespace
