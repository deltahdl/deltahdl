#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §31.4.1, Table 31-7: the $skew limit is a non-negative constant expression.
// A limit of zero is the boundary of the accepting path and must elaborate;
// this also exercises that a well-formed $skew parses and elaborates cleanly.
TEST(SystemTimingCheckElaboration, SkewZeroLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $skew(posedge clk1, negedge clk2, 0);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.4.1, Table 31-7 negative form: a negative literal $skew limit is
// rejected.
TEST(SystemTimingCheckElaboration, SkewNegativeLiteralLimitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $skew(posedge clk1, negedge clk2, -5);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$skew timing check limit must be a non-negative "
                            "constant expression",
                            3, "31.4.1"));
}

// §31.4.1, Table 31-7 negative form via a §31.2 specparam limit: a specparam
// whose value is negative is an illegal $skew limit and must be rejected.
TEST(SystemTimingCheckElaboration, SkewNegativeSpecparamLimitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tSkew = -3;\n"
      "    $skew(posedge clk1, negedge clk2, tSkew);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$skew timing check limit must be a non-negative "
                            "constant expression",
                            4, "31.4.1"));
}

// A non-negative specparam limit (the accepting path built from real §31.2
// syntax) elaborates without error.
TEST(SystemTimingCheckElaboration, SkewNonNegativeSpecparamLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tSkew = 4;\n"
      "    $skew(posedge clk1, negedge clk2, tSkew);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.4.1, Table 31-7: the limit is a constant *expression*, so an arithmetic
// combination of literals is a legal input form. One that folds to a negative
// value is rejected -- this drives the binary-fold path of the non-negative
// check, distinct from a bare negated literal.
TEST(SystemTimingCheckElaboration, SkewArithmeticLiteralLimitFoldsNegative) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $skew(posedge clk1, negedge clk2, 3 - 8);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$skew timing check limit must be a non-negative "
                            "constant expression",
                            3, "31.4.1"));
}

// Accepting counterpart: an arithmetic limit expression mixing a §31.2
// specparam operand with a literal that folds to a non-negative value
// elaborates cleanly (binary fold over an identifier operand).
TEST(SystemTimingCheckElaboration, SkewSpecparamArithmeticLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tSkew = 6;\n"
      "    $skew(posedge clk1, negedge clk2, tSkew - 2);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
