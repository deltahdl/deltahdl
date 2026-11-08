#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(RandomizeStdPackageParser, TheFormsOfTheSummaryParse) {
  auto r = Parse(
      "module m;\n"
      "  int a;\n"
      "  int b;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    ok = std::randomize();\n"
      "    ok = std::randomize(a);\n"
      "    ok = std::randomize(a, b);\n"
      "    ok = std::randomize(a, b) with { a < b; };\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(RandomizeStdPackageParser, AnArgumentShallBeAVariableIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ok = std::randomize(a, b + 1);\n"
      "    ok = std::randomize(1);\n"
      "    ok = std::randomize(c.d);\n"
      "    ok = std::randomize(arr[0]);\n"
      "    ok = std::randomize(a);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "argument to std::randomize shall be a variable identifier", 3,
      "G.5"));
  EXPECT_TRUE(ReportedError(
      r.diags, "argument to std::randomize shall be a variable identifier", 4,
      "G.5"));
  EXPECT_TRUE(ReportedError(
      r.diags, "argument to std::randomize shall be a variable identifier", 5,
      "G.5"));
  EXPECT_TRUE(ReportedError(
      r.diags, "argument to std::randomize shall be a variable identifier", 6,
      "G.5"));
  for (const auto& d : r.diags) {
    EXPECT_NE(d.loc.line, 7u);
  }
}

TEST(RandomizeStdPackageParser, TheClassMethodTakesVariableIdentifiersToo) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ok = obj.randomize(c.d);\n"
      "    ok = obj.randomize(arr[0]);\n"
      "  end\n"
      "endmodule\n");
  constexpr const char* kMessage =
      "randomize() arguments shall be object property names, not expressions";
  EXPECT_TRUE(ReportedError(r.diags, kMessage, 3, "18.11"));
  EXPECT_TRUE(ReportedError(r.diags, kMessage, 4, "18.11"));
}

}  // namespace
