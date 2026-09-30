#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(NamedSequenceDeclaration, ForwardInstantiationElaborates) {
  // §16.8: a named sequence may be instantiated anywhere a sequence_expr
  // may be written, including prior to its declaration. The elaborator
  // pre-populates the registry before walking items so a forward reference
  // resolves without error and without spurious cycle reports.
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
  // §16.8 cyclic dependency: s1 -> s2 -> s3 -> s1. The DFS in
  // PropertyRegistry::HasCyclicSequenceDependency must report a cycle for a
  // ring of three named sequences, not just two.
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
  // §16.8 scope list: an interface is a permitted scope for a named
  // sequence declaration; the elaborator should accept it without error.
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
  // §16.8: an instance shall provide an actual argument for each formal that
  // has no default. Sequence s has two non-default formals but is instantiated
  // with a single actual, so the instance is illegal. The instance is built
  // from a real §9.4.2.4 event control so the rule is observed end-to-end.
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
  // §16.8: a formal with a declared default actual argument need not be
  // supplied by the instance. Sequence s's second formal has a default, so a
  // single actual for the first formal is sufficient and elaboration succeeds.
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
  // §16.8: an instance cannot bind more positional actual arguments than the
  // sequence has formal arguments. Sequence s has one formal but is
  // instantiated with two actuals.
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

// §16.8: a formal referenced in a cycle delay range or a repetition bound
// takes an actual that is an elaboration-time constant. The clause's own
// delay_example: `a1` binds the constants 3 and 2 and `$`, and is legal;
// `a2_illegal` binds the variables z and d to min and delay1, and each is
// reported where the instance names it.
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

// §16.8 negative sibling: a parameter is an elaboration-time constant, so
// binding one where the delay_example's a2_illegal binds a variable is legal.
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

}  // namespace
