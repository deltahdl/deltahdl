#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(SeveritySystemTaskElab, FatalFinishNumberInRangeAccepted) {
  for (int fn = 0; fn <= 2; ++fn) {
    ElabFixture ef;
    auto src = "module m; $fatal(" + std::to_string(fn) + "); endmodule\n";
    auto* design = Elaborate(src, ef);
    ASSERT_NE(design, nullptr);
    EXPECT_FALSE(ef.has_errors)
        << "finish_number " << fn << " must elaborate cleanly";
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
  EXPECT_TRUE(ef.has_errors);
}

}  // namespace
