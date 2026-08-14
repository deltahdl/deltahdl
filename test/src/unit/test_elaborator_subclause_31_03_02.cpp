#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §31.3.2, Table 31-2: the $hold limit is a non-negative constant expression.
// A limit of zero is the boundary of the accepting path and must elaborate;
// this also exercises that a well-formed $hold parses and elaborates cleanly.
// Per Syntax 31-4 the reference_event is the first argument and the data_event
// the second.
TEST(HoldTimingCheckElaboration, ZeroLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $hold(posedge clk, data, 0);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.3.2, Table 31-2 negative form: a negative literal $hold limit is
// rejected.
TEST(HoldTimingCheckElaboration, NegativeLiteralLimitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $hold(posedge clk, data, -5);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$hold timing check limit must be a non-negative "
                            "constant expression",
                            3, "31.3.2"));
}

// §31.3.2, Table 31-2 negative form via a §31.2 specparam limit: a specparam
// whose value is negative is an illegal $hold limit and must be rejected. The
// limit is built from real specparam syntax so the validator folds the
// specparam reference to its negative value.
TEST(HoldTimingCheckElaboration, NegativeSpecparamLimitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tHold = -3;\n"
      "    $hold(posedge clk, data, tHold);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$hold timing check limit must be a non-negative "
                            "constant expression",
                            4, "31.3.2"));
}

// A non-negative specparam limit (the accepting path built from real §31.2
// syntax) elaborates without error.
TEST(HoldTimingCheckElaboration, NonNegativeSpecparamLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tHold = 4;\n"
      "    $hold(posedge clk, data, tHold);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.3.2, Table 31-2: the non-negative constant limit may be an arithmetic
// combination of a §31.2 specparam and a literal, not just a bare operand. The
// elaborator folds the expression; a result that stays non-negative is
// accepted. This drives the binary-fold path, distinct from the bare-literal
// and bare-specparam input forms above.
TEST(HoldTimingCheckElaboration, NonNegativeArithmeticLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tHold = 3;\n"
      "    $hold(posedge clk, data, tHold + 2);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.3.2, Table 31-2 negative form via a constant arithmetic expression: a
// specparam-and-literal combination that folds to a negative value is an
// illegal $hold limit and is rejected. This exercises the binary-fold path to a
// negative result, distinct from the bare-literal and bare-specparam negative
// forms above.
TEST(HoldTimingCheckElaboration, NegativeArithmeticLimitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tHold = 3;\n"
      "    $hold(posedge clk, data, tHold - 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$hold timing check limit must be a non-negative "
                            "constant expression",
                            4, "31.3.2"));
}

}  // namespace
