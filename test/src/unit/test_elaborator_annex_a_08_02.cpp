#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(SubroutineCallExprElaboration, MethodCallElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin obj.method(); end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallElaborationSyntax, SystemCallStatementElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial $display(\"hello\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, TfCallNoArgsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task t; endtask\n"
      "  initial t();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, TfCallWithPositionalArgsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int f(int a, int b); return a + b; endfunction\n"
      "  int x;\n"
      "  initial x = f(1, 2);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, ConstantFunctionCallInParameterElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int f(int a); return a + 1; endfunction\n"
      "  parameter P = f(3);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, SystemTfCallBareElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial $finish;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, NamedArgumentsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int f(int a, int b); return a - b; endfunction\n"
      "  int x;\n"
      "  initial x = f(.a(10), .b(3));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, MixedPositionalAndNamedArgsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int f(int a, int b, int c); return a + b + c; endfunction\n"
      "  int x;\n"
      "  initial x = f(1, 2, .c(3));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, RandomizeBasicElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin obj.randomize(); end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, TaskCallWithoutParensElaborates) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t; endtask\n"
      "  initial t;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, VoidFunctionCallWithoutParensElaborates) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void log; endfunction\n"
      "  initial log;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, NonVoidFunctionCallWithoutParensRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int f; return 1; endfunction\n"
      "  initial f;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, ScopeRandomizeWithNullRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin randomize(null); end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, StdRandomizeWithNullRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin std::randomize(null); end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(SubroutineCallExprElaboration, ScopeRandomizeWithParenIdListRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin randomize() with (a) { a > 0; }; end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(SubroutineCallExprElaboration,
     ClassMethodRandomizeWithParenIdListAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin obj.randomize() with (a) { a > 0; }; end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// constant_function_call folded in a constant-expression context where the
// call's argument is itself a parameter (a distinct constant form from the
// literal used in ConstantFunctionCallInParameterElaborates). The elaborator
// must resolve the parameter before folding the call.
TEST(SubroutineCallExprElaboration, ConstantFunctionCallWithParameterArg) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int B = 41;\n"
      "  function int inc(int n); return n + 1; endfunction\n"
      "  localparam int P = inc(B);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// constant_function_call folded where the argument is a localparam constant.
TEST(SubroutineCallExprElaboration, ConstantFunctionCallWithLocalparamArg) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam int B = 41;\n"
      "  function int inc(int n); return n + 1; endfunction\n"
      "  localparam int P = inc(B);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
