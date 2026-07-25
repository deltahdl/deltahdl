#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §31.3.4, Table 31-4: the $removal limit is a non-negative constant
// expression. A limit of zero is the boundary of the accepting path and must
// elaborate; this also exercises that a well-formed $removal parses and
// elaborates cleanly. Per Syntax 31-6 the reference_event is the first argument
// and the data_event the second.
TEST(RemovalTimingCheckElaboration, ZeroLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $removal(posedge rst, clk, 0);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.3.4, Table 31-4 negative form: a negative literal $removal limit is
// rejected. This is the closest input the non-negative rule must reject, driven
// from a bare literal operand.
TEST(RemovalTimingCheckElaboration, NegativeLiteralLimitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $removal(posedge rst, clk, -5);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §31.3.4, Table 31-4 negative form via a §31.2 specparam limit: a specparam
// whose value is negative is an illegal $removal limit and must be rejected.
// The limit is built from real specparam syntax so the validator folds the
// specparam reference to its negative value.
TEST(RemovalTimingCheckElaboration, NegativeSpecparamLimitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tRem = -3;\n"
      "    $removal(posedge rst, clk, tRem);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// A non-negative specparam limit (the accepting path built from real §31.2
// syntax) elaborates without error -- the constant-expression form of the limit
// beyond a bare literal.
TEST(RemovalTimingCheckElaboration, NonNegativeSpecparamLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tRem = 4;\n"
      "    $removal(posedge rst, clk, tRem);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.3.4, Table 31-4: the non-negative constant limit may be an arithmetic
// combination of a §31.2 specparam and a literal, not just a bare operand. The
// elaborator folds the expression; a result that stays non-negative is
// accepted. This drives the binary-fold path, distinct from the bare-literal
// and bare-specparam input forms above.
TEST(RemovalTimingCheckElaboration, NonNegativeArithmeticLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tRem = 3;\n"
      "    $removal(posedge rst, clk, tRem + 2);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.3.4, Table 31-4 negative form via a constant arithmetic expression: a
// specparam-and-literal combination that folds to a negative value is an
// illegal $removal limit and is rejected. This exercises the binary-fold path
// to a negative result, distinct from the bare-literal and bare-specparam
// negative forms above.
TEST(RemovalTimingCheckElaboration, NegativeArithmeticLimitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tRem = 3;\n"
      "    $removal(posedge rst, clk, tRem - 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
