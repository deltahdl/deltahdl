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
    // The finish_number is accepted: the $fatal reports itself (§20.10.1)
    // and nothing stands on the argument (§20.10).
    EXPECT_TRUE(ReportedError(ef.diag.Diagnostics(),
                              "elaboration FATAL in scope 'm'", 1, "20.10.1"))
        << "finish_number " << fn;
    EXPECT_FALSE(ReportedError(ef.diag.Diagnostics(),
                               "finish_number must be 0, 1, or 2", 1, "20.10"))
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
