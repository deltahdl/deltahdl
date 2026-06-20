#include "fixture_elaborator.h"

namespace {

TEST(ElaborationSeverityTaskElab, InfoDoesNotCauseError) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  $info(\"build info\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElaborationSeverityTaskElab, WarningDoesNotCauseError) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  $warning(\"potential issue\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElaborationSeverityTaskElab, FatalValidFinishNumbers) {
  for (int fn = 0; fn <= 2; ++fn) {
    ElabFixture f;
    auto src = "module m; $fatal(" + std::to_string(fn) + "); endmodule\n";
    auto* design = Elaborate(src, f);
    ASSERT_NE(design, nullptr);
    EXPECT_FALSE(f.has_errors) << "finish_number " << fn << " should be valid";
  }
}

TEST(ElaborationSeverityTaskElab, FatalInvalidFinishNumber) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  $fatal(3);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

TEST(ElaborationSeverityTaskElab, FatalNoArgsIsValid) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  $fatal;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
