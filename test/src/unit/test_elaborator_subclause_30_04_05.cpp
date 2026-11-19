#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(FullAndParallelConnectionElaboration, VectorAndScalarEndpointsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input sel, input [7:0] in1, in2, output [7:0] q,\n"
      "         output qs);\n"
      "  specify\n"
      "    (in1 => q) = 3;\n"
      "    (sel *> q) = 2;\n"
      "    (sel => qs) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FullAndParallelConnectionElaboration, FullAllowsDifferentWidthVectors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input [7:0] a, output [3:0] b);\n"
      "  specify\n"
      "    (a *> b) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FullAndParallelConnectionElaboration, FullAllowsVectorToScalar) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input [7:0] a, output b);\n"
      "  specify\n"
      "    (a *> b) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FullAndParallelConnectionElaboration, ScalarPairAcceptsEitherOperator) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output b);\n"
      "  specify\n"
      "    (a => b) = 1;\n"
      "    (a *> b) = 2;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FullAndParallelConnectionElaboration, ErrorParallelWidthMismatch) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input [7:0] a, output [3:0] b);\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parallel path source and destination must have "
                            "equal bit widths",
                            3, "30.4.5"));
}

TEST(FullAndParallelConnectionElaboration, ParallelEqualWidthPartSelects) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input [7:0] a, output [7:0] b);\n"
      "  specify\n"
      "    (a[5:2] => b[3:0]) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FullAndParallelConnectionElaboration,
     ErrorParallelPartSelectWidthMismatch) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input [7:0] a, output [7:0] b);\n"
      "  specify\n"
      "    (a[5:2] => b[1:0]) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parallel path source and destination must have "
                            "equal bit widths",
                            3, "30.4.5"));
}

TEST(FullAndParallelConnectionElaboration, FullAllowsPartSelectWidthMismatch) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input [7:0] a, output [7:0] b);\n"
      "  specify\n"
      "    (a[5:2] *> b[1:0]) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FullAndParallelConnectionElaboration, ParallelBitSelectsEqualWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input [7:0] a, output [7:0] b);\n"
      "  specify\n"
      "    (a[3] => b[5]) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FullAndParallelConnectionElaboration,
     ErrorParallelBitSelectWidthMismatch) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input [7:0] a, output [7:0] b);\n"
      "  specify\n"
      "    (a[3] => b[1:0]) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parallel path source and destination must have "
                            "equal bit widths",
                            3, "30.4.5"));
}

TEST(FullAndParallelConnectionElaboration, ParallelPlusIndexedEqualWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input [7:0] a, output [7:0] b);\n"
      "  specify\n"
      "    (a[0+:4] => b[3:0]) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FullAndParallelConnectionElaboration,
     ErrorParallelPlusIndexedWidthMismatch) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input [7:0] a, output [7:0] b);\n"
      "  specify\n"
      "    (a[0+:4] => b[1:0]) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parallel path source and destination must have "
                            "equal bit widths",
                            3, "30.4.5"));
}

TEST(FullAndParallelConnectionElaboration, ParallelMinusIndexedEqualWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input [7:0] a, output [7:0] b);\n"
      "  specify\n"
      "    (a[3-:4] => b[3:0]) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

std::string ConnectionModule(const std::string& header,
                             const std::string& path) {
  return "module m" + header + ";\n  specify\n    " + path +
         "\n  endspecify\nendmodule\n";
}

void ExpectConnectionAccepted(const std::string& header,
                              const std::string& path) {
  ElabFixture f;
  auto* design = ElaborateSrc(ConnectionModule(header, path), f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

void ExpectParallelWidthReported(const std::string& header,
                                 const std::string& path) {
  ElabFixture f;
  ElaborateSrc(ConnectionModule(header, path), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parallel path source and destination must have "
                            "equal bit widths",
                            3, "30.4.5"));
}

constexpr char kGuardedPorts[] = "(input c, input [7:0] a, output [3:0] b)";

TEST(FullAndParallelConnectionElaboration,
     ErrorStateDependentParallelWidthMismatch) {
  ExpectParallelWidthReported(kGuardedPorts, "if (c) (a => b) = 5;");
}

TEST(FullAndParallelConnectionElaboration,
     StateDependentParallelEqualWidthElaborates) {
  ExpectConnectionAccepted(kGuardedPorts, "if (c) (a[3:0] => b) = 5;");
}

TEST(FullAndParallelConnectionElaboration, ErrorIfnoneParallelWidthMismatch) {
  ExpectParallelWidthReported(kGuardedPorts, "ifnone (a => b) = 5;");
}

TEST(FullAndParallelConnectionElaboration, IfnoneParallelEqualWidthElaborates) {
  ExpectConnectionAccepted(kGuardedPorts, "ifnone (a[7:4] => b) = 5;");
}

TEST(FullAndParallelConnectionElaboration, ErrorParallelScalarToVector) {
  ExpectParallelWidthReported("(input s, output [3:0] b)", "(s => b) = 5;");
}

TEST(FullAndParallelConnectionElaboration, FullScalarToVectorElaborates) {
  ExpectConnectionAccepted("(input s, output [3:0] b)", "(s *> b) = 5;");
}

TEST(FullAndParallelConnectionElaboration, ErrorParallelVectorToScalar) {
  ExpectParallelWidthReported("(input [3:0] a, output y)", "(a => y) = 5;");
}

TEST(FullAndParallelConnectionElaboration,
     ParallelAscendingToDescendingEqualWidth) {
  ExpectConnectionAccepted("(input [0:3] a, output [7:4] b)", "(a => b) = 5;");
}

TEST(FullAndParallelConnectionElaboration,
     ErrorParallelAscendingRangeWidthMismatch) {
  ExpectParallelWidthReported("(input [0:4] a, output [7:4] b)",
                              "(a => b) = 5;");
}

TEST(FullAndParallelConnectionElaboration,
     ErrorParallelParameterWidthMismatch) {
  ExpectParallelWidthReported(
      " #(parameter W = 8)(input [W-1:0] a, output [3:0] b)", "(a => b) = 5;");
}

TEST(FullAndParallelConnectionElaboration,
     DISABLED_ParallelParameterEqualWidth) {
  ExpectConnectionAccepted(
      " #(parameter W = 4)(input [W-1:0] a, output [3:0] b)", "(a => b) = 5;");
}

TEST(FullAndParallelConnectionElaboration,
     FullMixedWidthSourcesAndDestinations) {
  ExpectConnectionAccepted("(input s, input [7:0] a, output [3:0] b, output y)",
                           "(s, a *> b, y) = 5;");
}

TEST(FullAndParallelConnectionElaboration, MultiplexerExampleElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module mux8(in1, in2, s, q);\n"
      "  output [7:0] q;\n"
      "  input [7:0] in1, in2;\n"
      "  input s;\n"
      "  specify\n"
      "    (in1 => q) = (3, 4);\n"
      "    (in2 => q) = (2, 3);\n"
      "    (s *> q) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

std::string OverriddenWidthDesign(int default_width, int override_width) {
  return "module m #(parameter W = " + std::to_string(default_width) +
         ")(input [W-1:0] a, output [3:0] b);\n"
         "  specify\n"
         "    (a => b) = 5;\n"
         "  endspecify\n"
         "endmodule\n"
         "module top;\n"
         "  logic [7:0] a;\n"
         "  wire [3:0] b;\n"
         "  m #(.W(" +
         std::to_string(override_width) +
         ")) u(.a(a), .b(b));\n"
         "endmodule\n";
}

TEST(FullAndParallelConnectionElaboration,
     DISABLED_ParallelParameterOverriddenToEqualWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(OverriddenWidthDesign(8, 4), f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FullAndParallelConnectionElaboration,
     ErrorParallelParameterOverriddenToUnequalWidth) {
  ElabFixture f;
  ElaborateSrc(OverriddenWidthDesign(4, 8), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parallel path source and destination must have "
                            "equal bit widths",
                            3, "30.4.5"));
}

}  // namespace
