#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §31.3.5, Table 31-5: the $recovery limit is a non-negative constant
// expression. A limit of zero is the boundary of the accepting path and must
// elaborate; this also exercises that a well-formed $recovery parses and
// elaborates cleanly. Per Syntax 31-7 the reference_event is the first argument
// and the data_event the second.
TEST(RecoveryTimingCheckElaboration, ZeroLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $recovery(posedge rst, clk, 0);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.3.5, Table 31-5 negative form: a negative literal $recovery limit is
// rejected. This is the closest input the non-negative rule must reject, driven
// from a bare literal operand.
TEST(RecoveryTimingCheckElaboration, NegativeLiteralLimitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $recovery(posedge rst, clk, -5);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §31.3.5, Table 31-5 negative form via a §31.2 specparam limit: a specparam
// whose value is negative is an illegal $recovery limit and must be rejected.
// The limit is built from real specparam syntax so the validator folds the
// specparam reference to its negative value.
TEST(RecoveryTimingCheckElaboration, NegativeSpecparamLimitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tRec = -3;\n"
      "    $recovery(posedge rst, clk, tRec);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// A non-negative specparam limit (the accepting path built from real §31.2
// syntax) elaborates without error -- the constant-expression form of the limit
// beyond a bare literal.
TEST(RecoveryTimingCheckElaboration, NonNegativeSpecparamLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tRec = 4;\n"
      "    $recovery(posedge rst, clk, tRec);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.3.5, Table 31-5: the non-negative constant limit may be an arithmetic
// combination of a §31.2 specparam and a literal, not just a bare operand. The
// elaborator folds the expression; a result that stays non-negative is
// accepted. This drives the binary-fold path, distinct from the bare-literal
// and bare-specparam input forms above.
TEST(RecoveryTimingCheckElaboration, NonNegativeArithmeticLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tRec = 3;\n"
      "    $recovery(posedge rst, clk, tRec + 2);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.3.5, Table 31-5 negative form via a constant arithmetic expression: a
// specparam-and-literal combination that folds to a negative value is an
// illegal $recovery limit and is rejected. This exercises the binary-fold path
// to a negative result, distinct from the bare-literal and bare-specparam
// negative forms above.
TEST(RecoveryTimingCheckElaboration, NegativeArithmeticLimitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tRec = 3;\n"
      "    $recovery(posedge rst, clk, tRec - 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
