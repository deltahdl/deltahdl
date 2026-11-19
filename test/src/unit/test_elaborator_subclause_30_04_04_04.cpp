#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(IfnoneConditionElaboration, ParallelPathElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    ifnone (a => b) = 15;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(IfnoneConditionElaboration, MatchingCompanionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    if (c) (a => y) = 1;\n"
      "    ifnone (a => y) = 2;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(IfnoneConditionElaboration, MatchingEdgeSensitiveCompanionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    if (c) (posedge clk => q) = (1, 2);\n"
      "    ifnone (clk => q) = (3, 4);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(IfnoneConditionElaboration, IfnoneFromAnotherSourceElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    if (c) (a => y) = 1;\n"
      "    ifnone (b => y) = 2;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(IfnoneConditionElaboration, IfnoneToAnotherDestinationElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, c, output y, z);\n"
      "  specify\n"
      "    if (c) (a => y) = 1;\n"
      "    ifnone (a => z) = 2;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(IfnoneConditionElaboration, ErrorCoexistsWithUnconditional) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    ifnone (a => b) = 1;\n"
      "    (a => b) = 2;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "conflicts with an unconditional path on the same endpoints", 3,
      "30.4.4.4"));
}

TEST(IfnoneConditionElaboration, MatchingFullConnectionCompanionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    if (c) (a, b *> z) = 10;\n"
      "    ifnone (a, b *> z) = 20;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(IfnoneConditionElaboration, UnrelatedUnconditionalCoexists) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    ifnone (a => b) = 1;\n"
      "    (c => d) = 2;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(IfnoneConditionElaboration, UnconditionalEdgeSensitivePathCoexists) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input clk, d, output q);\n"
      "  specify\n"
      "    (posedge clk => (q : d)) = 1;\n"
      "    ifnone (clk => q) = 2;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(IfnoneConditionElaboration, ConflictAcrossSpecifyBlocksIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input a, output b);\n"
      "  specify\n"
      "    (a => b) = 2;\n"
      "  endspecify\n"
      "  specify\n"
      "    ifnone (a => b) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "conflicts with an unconditional path on the same endpoints", 6,
      "30.4.4.4"));
}

TEST(IfnoneConditionElaboration, ErrorFullConnectionPairWithUnconditional) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input a, input b, output z);\n"
      "  specify\n"
      "    ifnone (a, b *> z) = 1;\n"
      "    (a, b *> z) = 2;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "conflicts with an unconditional path on the same endpoints", 3,
      "30.4.4.4"));
}

TEST(IfnoneConditionElaboration,
     ErrorUnconditionalWithOtherConnectionOperator) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input a, output w);\n"
      "  specify\n"
      "    ifnone (a => w) = 1;\n"
      "    (a *> w) = 2;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "conflicts with an unconditional path on the same endpoints", 3,
      "30.4.4.4"));
}

TEST(IfnoneConditionElaboration,
     IfnoneBesideOperationConditionedPathsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module ALU(o1, i1, i2, opcode);\n"
      "  input [7:0] i1, i2;\n"
      "  input [2:1] opcode;\n"
      "  output [7:0] o1;\n"
      "  specify\n"
      "    if (opcode == 2'b00) (i1, i2 *> o1) = (25.0, 25.0);\n"
      "    if (opcode == 2'b01) (i1 => o1) = (5.6, 8.0);\n"
      "    if (opcode == 2'b10) (i2 => o1) = (5.6, 8.0);\n"
      "    ifnone (i2 => o1) = (15.0, 15.0);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
