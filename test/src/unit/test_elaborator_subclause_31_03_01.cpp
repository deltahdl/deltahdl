#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §31.3.1, Table 31-1: the $setup limit is a "Non-negative constant
// expression". Syntax 31-3 writes the data event first and the reference event
// second. A limit of zero is the boundary of the accepting path.
TEST(SetupTimingCheckElaboration, ZeroLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input d, clk);\n"
      "  specify\n"
      "    $setup(d, posedge clk, 0);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// A negative literal limit is refused. §31.9 (printed page 919) lets "Both the
// $setuphold and $recrem timing checks" accept negative values, and $setup is
// neither.
TEST(SetupTimingCheckElaboration, NegativeLiteralLimitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input d, clk);\n"
      "  reg n = 0;\n"
      "  specify\n"
      "    $setup(d, posedge clk, -5, n);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$setup timing check limit must be a non-negative "
                            "constant expression",
                            4, "31.3.1"));
}

// The same through a specparam whose value is negative (§31.2: a limit is a
// constant expression that can include specparams).
TEST(SetupTimingCheckElaboration, NegativeSpecparamLimitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input d, clk);\n"
      "  specify\n"
      "    specparam tSU = -3;\n"
      "    $setup(d, posedge clk, tSU);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$setup timing check limit must be a non-negative "
                            "constant expression",
                            4, "31.3.1"));
}

// A limit expression that folds to a non-negative value is accepted.
TEST(SetupTimingCheckElaboration, NonNegativeSpecparamExpressionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input d, clk);\n"
      "  specify\n"
      "    specparam tSU = 7;\n"
      "    $setup(d, posedge clk, tSU - 2);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
