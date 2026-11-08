#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(NamedSequenceDeclaration, ForwardInstantiationElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b, c;\n"
      "  sequence early;\n"
      "    @(posedge clk) (a ##1 late);\n"
      "  endsequence\n"
      "  sequence late;\n"
      "    @(posedge clk) b ##1 c;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NamedSequenceDeclaration, AcyclicSequenceRegistryElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, x, y;\n"
      "  sequence s1;\n"
      "    @(posedge clk) x ##1 y;\n"
      "  endsequence\n"
      "  sequence s2;\n"
      "    @(posedge clk) s1 ##1 y;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NamedSequenceDeclaration, CyclicTwoSequencesIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, x, y;\n"
      "  sequence s1;\n"
      "    @(posedge clk) (x ##1 s2);\n"
      "  endsequence\n"
      "  sequence s2;\n"
      "    @(posedge clk) (y ##1 s1);\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cyclic dependency among named sequences involving \"s1\"", 3, "16.8"));
}

TEST(NamedSequenceDeclaration, ThreeNodeCycleIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, x, y, z;\n"
      "  sequence s1;\n"
      "    @(posedge clk) (x ##1 s2);\n"
      "  endsequence\n"
      "  sequence s2;\n"
      "    @(posedge clk) (y ##1 s3);\n"
      "  endsequence\n"
      "  sequence s3;\n"
      "    @(posedge clk) (z ##1 s1);\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cyclic dependency among named sequences involving \"s1\"", 3, "16.8"));
}

TEST(NamedSequenceDeclaration, SequenceInInterfaceScopeElaborates) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc;\n"
      "  logic clk, a, b;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "endinterface\n"
      "module m;\n"
      "  ifc i ();\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(NamedSequenceDeclaration, TooFewActualsForNonDefaultFormalsIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, x;\n"
      "  sequence s(a, b);\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "  initial @(s(x)) $display(\"go\");\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "sequence instance omits an actual argument for a "
                            "formal that has no default",
                            6, "16.8"));
}

TEST(NamedSequenceDeclaration, DefaultFormalAllowsOmittedActual) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, x;\n"
      "  sequence s(a, b = 1'b1);\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "  initial @(s(x)) $display(\"go\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NamedSequenceDeclaration, TooManyActualsIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, x, y;\n"
      "  sequence s(a);\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "  initial @(s(x, y)) $display(\"go\");\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "sequence instance provides more actual arguments "
                            "than the sequence has formal arguments",
                            6, "16.8"));
}

TEST(NamedSequenceDeclaration, SelfRecursiveSequenceIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, x;\n"
      "  sequence sr;\n"
      "    @(posedge clk) (x ##1 sr);\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cyclic dependency among named sequences involving \"sr\"", 3, "16.8"));
}

TEST(NamedSequenceDeclaration, VariableActualForADelayOrRepetitionFormal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  bit x, y;\n"
      "  int z, d;\n"
      "  sequence delay_example(x, y, min, max, delay1);\n"
      "    x ##delay1 y[*min:max];\n"
      "  endsequence\n"
      "  a1: assert property (@(posedge clk) delay_example(x, y, 3, $, 2));\n"
      "  a2_illegal: assert property (@(posedge clk)\n"
      "    delay_example(x, y, z, $, d));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the actual argument 'z' bound to the formal "
                            "'min' of sequence 'delay_example' is not an "
                            "elaboration-time constant",
                            10, "16.8"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the actual argument 'd' bound to the formal "
                            "'delay1' of sequence 'delay_example' is not an "
                            "elaboration-time constant",
                            10, "16.8"));
}

TEST(NamedSequenceDeclaration, ParameterActualForADelayFormalIsAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  bit x, y;\n"
      "  parameter int P = 2;\n"
      "  sequence delay_example(x, y, min, max, delay1);\n"
      "    x ##delay1 y[*min:max];\n"
      "  endsequence\n"
      "  a1: assert property (@(posedge clk) delay_example(x, y, P, $, P));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SequenceCycleElaboration, ACycleThroughAFormalsDefaultIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a;\n"
      "  sequence s1(x = s2);\n"
      "    x ##1 a;\n"
      "  endsequence\n"
      "  sequence s2;\n"
      "    s1 ##1 a;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cyclic dependency among named sequences "
                            "involving \"s1\"",
                            3, "16.8"));
}

TEST(SequenceDollarActual, ATypedOrOperandFormalIsReported) {
  const char* const kReport =
      "shall be untyped and referenced only as the upper bound of a cycle "
      "delay range or as an actual argument of an instance";
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a, b;\n"
      "  sequence s1(int n);\n"
      "    a ##[1:n] b;\n"
      "  endsequence\n"
      "  sequence s2(m);\n"
      "    a ##1 (b == m);\n"
      "  endsequence\n"
      "  sequence s3(k);\n"
      "    a ##[1:k] b;\n"
      "  endsequence\n"
      "  a1: assert property (@(posedge clk) s1($));\n"
      "  a2: assert property (@(posedge clk) s2($));\n"
      "  a3: assert property (@(posedge clk) s3($));\n"
      "  sequence s4(k, j);\n"
      "    a ##[j:$] b ##[1:k] b;\n"
      "  endsequence\n"
      "  sequence s5(x, m = $);\n"
      "    a ##[1:m] x;\n"
      "  endsequence\n"
      "  sequence s6(k);\n"
      "    a ##1 s3(k);\n"
      "  endsequence\n"
      "  a4: assert property (@(posedge clk) s4($, 1));\n"
      "  a5: assert property (@(posedge clk) s5(b));\n"
      "  a6: assert property (@(posedge clk) s6($));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 12, "16.8"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 13, "16.8"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 14, "16.8"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 24, "16.8"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 25, "16.8"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 26, "16.8"));
}

}  // namespace
