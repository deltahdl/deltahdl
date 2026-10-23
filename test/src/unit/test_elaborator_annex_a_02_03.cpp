#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(DeclarationListElaboration, MultipleNetsElaborate) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b, c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->nets.size(), 3u);
}

TEST(DeclarationListElaboration, MultipleParamsElaborate) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter A = 1, B = 2, C = 3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  int count = 0;
  for (auto& p : mod->params) {
    if (p.name == "A" || p.name == "B" || p.name == "C") count++;
  }
  EXPECT_EQ(count, 3);
}

TEST(DeclarationListElaboration, MultipleGenvarsElaborate) {
  EXPECT_TRUE(ElabOk("module m; genvar i, j; endmodule"));
}

TEST(DeclarationListElaboration, MultiplePortsElaborate) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m(input logic a, input logic b, output logic c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->ports.size(), 3u);
}

TEST(DeclarationListElaboration, TypeParamsElaborate) {
  EXPECT_TRUE(
      ElabOk("module m; parameter type T1 = int, T2 = real; endmodule"));
}

// A.2.3's list_of_port_identifiers gives a non-ANSI net port's name
// unpacked_dimensions alone, so a dynamic dimension on an input declared with
// no type, a net (§23.2.2.3), is reported. It was taken with no report.
TEST(DeclarationListElaboration, ANonAnsiNetPortOfADynamicDimensionIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module n(d);\n"
      "  input d [];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "net port 'd' takes fixed-size unpacked dimensions "
                            "alone; a dynamic, associative or queue dimension "
                            "belongs to a variable port",
                            1, "A.2.3"));
}

// A.2.3's list_of_variable_port_identifiers gives a non-ANSI variable output
// variable_dimensions, so its queue dimension draws no report. It was reported
// as an unpacked dimension that is not a constant expression (§7.4.2).
TEST(DeclarationListElaboration, ANonAnsiVariablePortTakesAQueueDimension) {
  ElabFixture f;
  ElaborateSrc(
      "module n(q);\n"
      "  output int q [$];\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
