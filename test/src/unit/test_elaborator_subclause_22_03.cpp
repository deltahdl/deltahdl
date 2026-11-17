#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ResetAllElaboration, ResetsDelayModeForElaboration) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`delay_mode_zero\n"
      "`resetall\n"
      "module t;\n"
      "  parameter P = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->top_modules[0]->delay_mode, DelayModeDirective::kNone);
}

TEST(ResetAllElaboration, PreservesMacroValuesForElaboration) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`define VAL 55\n"
      "`resetall\n"
      "module t;\n"
      "  parameter P = `VAL;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& p : mod->params) {
    if (p.name == "P") {
      EXPECT_EQ(p.resolved_value, 55);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(ResetAllElaboration, InsideExcludedBranchDoesNotAffectElaboration) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`delay_mode_unit\n"
      "`ifdef UNDEF\n"
      "`resetall\n"
      "`endif\n"
      "module t;\n"
      "  parameter P = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->top_modules[0]->delay_mode, DelayModeDirective::kUnit);
}

TEST(ResetAllElaboration, ImplicitNetsAreWireOnlyAfterTheDirective) {
  ElabFixture f;
  ElaborateWithPreprocessor(
      "`default_nettype none\n"
      "module m1;\n"
      "  assign x1 = 1'b0;\n"
      "endmodule\n"
      "`resetall\n"
      "module m2;\n"
      "  assign x2 = 1'b0;\n"
      "endmodule\n",
      f, "", true);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "implicit net 'x1' forbidden by `default_nettype none", 3, "22.8"));
  for (const auto& d : f.diag.Diagnostics()) {
    EXPECT_EQ(d.message.find("x2"), std::string::npos) << d.message;
  }
}

TEST(ResetAllElaboration, AModuleAfterTheDirectiveHasNoTimescale) {
  ElabFixture f;
  ElaborateWithPreprocessor(
      "`timescale 1us / 1ns\n"
      "module m1;\n"
      "endmodule\n"
      "`resetall\n"
      "module m2;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "some design elements specify time unit and "
                            "precision while others do not",
                            5, "3.14.2.3"));
}

}  // namespace
