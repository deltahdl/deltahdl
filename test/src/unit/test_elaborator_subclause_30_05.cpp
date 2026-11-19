#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(SpecifyPathDelayElaboration, RejectsNonSpecparamIdentifier) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire [31:0] w;\n"
      "  assign w = 5;\n"
      "  specify\n"
      "    (a => b) = w;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "module path delay operand 'w' is not a specparam",
                            5, "30.5"));
}

TEST(SpecifyPathDelayElaboration, AcceptsSpecparamIdentifier) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tPD = 5;\n"
      "    (a => b) = tPD;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecifyPathDelayElaboration, AcceptsLiteralPlusSpecparamExpression) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tRise = 3;\n"
      "    (a => b) = tRise + 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecifyPathDelayElaboration, RejectsModuleParameterOperand) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  parameter P = 5;\n"
      "  specify\n"
      "    (a => b) = P;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "module path delay operand 'P' is not a specparam",
                            4, "30.5"));
}

TEST(SpecifyPathDelayElaboration, AcceptsLiteralValue) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecifyPathDelayElaboration, AcceptsMinTypMaxDelayFromSpecparams) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tmin = 1, ttyp = 2, tmax = 3;\n"
      "    (a => b) = tmin:ttyp:tmax;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecifyPathDelayElaboration, RejectsMinTypMaxWithNonSpecparamOperand) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire [31:0] w;\n"
      "  assign w = 2;\n"
      "  specify\n"
      "    specparam tmin = 1, tmax = 3;\n"
      "    (a => b) = tmin:w:tmax;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "module path delay operand 'w' is not a specparam",
                            6, "30.5"));
}

bool PathOperandReported(const std::string& decl, const std::string& path,
                         const std::string& operand, int line) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input a, input clk, input en, input d, output y, "
      "output q);\n" +
          decl + "\n  specify\n    " + path + "\n  endspecify\nendmodule\n",
      f);
  return ReportedError(
      f.diag.Diagnostics(),
      "module path delay operand '" + operand + "' is not a specparam", line,
      "30.5");
}

TEST(SpecifyPathDelayElaboration, RejectsVariableOperand) {
  EXPECT_TRUE(PathOperandReported("  int v = 5;", "(a => y) = v;", "v", 4));
}

TEST(SpecifyPathDelayElaboration, RejectsLocalparamOperand) {
  EXPECT_TRUE(
      PathOperandReported("  localparam L = 5;", "(a => y) = L;", "L", 4));
}

TEST(SpecifyPathDelayElaboration, RejectsPortOperand) {
  EXPECT_TRUE(PathOperandReported("", "(a => y) = d;", "d", 4));
}

TEST(SpecifyPathDelayElaboration, RejectsOperandInALaterListPosition) {
  EXPECT_TRUE(
      PathOperandReported("  int v = 5;", "(a => y) = (5, v);", "v", 4));
}

TEST(SpecifyPathDelayElaboration, RejectsOperandOnAnEdgeSensitivePath) {
  EXPECT_TRUE(PathOperandReported("  int v = 5;",
                                  "(posedge clk => (q : d)) = v;", "v", 4));
}

TEST(SpecifyPathDelayElaboration, RejectsOperandOnAStateDependentPath) {
  EXPECT_TRUE(
      PathOperandReported("  int v = 5;", "if (en) (a => y) = v;", "v", 4));
}

TEST(SpecifyPathDelayElaboration, DISABLED_RejectsUserFunctionCallOperand) {
  EXPECT_TRUE(PathOperandReported(
      "  function automatic int f(int x); return x; endfunction",
      "(a => y) = f(3);", "f", 4));
}

TEST(SpecifyPathDelayElaboration, DISABLED_RejectsSystemFunctionCallOperand) {
  EXPECT_TRUE(PathOperandReported("", "(a => y) = $clog2(8);", "$clog2", 4));
}

TEST(SpecifyPathDelayElaboration, AcceptsModuleBodySpecparam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output y);\n"
      "  specparam tb = 7;\n"
      "  specify\n"
      "    (a => y) = tb;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
