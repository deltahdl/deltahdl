#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// The resolved value of the named localparam of the single elaborated top
// module, or -1 where it is absent or was left unresolved, so that a fold that
// never happened is told from one that happened (§13.4.3), as in
// test_elaborator_subclause_13_04_03a.cpp.
int64_t ResolvedParam(RtlirDesign* design, std::string_view name) {
  if (!design || design->top_modules.empty()) return -1;
  for (const auto& p : design->top_modules[0]->params) {
    if (p.name == name) return p.is_resolved ? p.resolved_value : -1;
  }
  return -1;
}

// §13.4.3 lets a constant function be declared in a package and called in a
// parameter initializer, and §26.3 names a package's function through the
// package scope resolution operator or an import (printed pages 345 and 808
// of IEEE 1800-2023). The folder registered a module's own functions
// alone and declined a call with no bare callee, so `pk::twice(6)` never folded
// and P was left unresolved.
TEST(ConstantFunctionElaboration, PackageFunctionThroughPackageScopeFolds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package pk;\n"
      "  function automatic int twice(int a); return a * 2; endfunction\n"
      "endpackage\n"
      "module m;\n"
      "  localparam int P = pk::twice(6);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(ResolvedParam(design, "P"), 12);
}

// The same function reached by a wildcard import, with its defaulted second
// argument (§13.5.3) left to the default, and through the package scope with
// both actuals written: 6 * 2 and 7 * 1.
TEST(ConstantFunctionElaboration, ImportedPackageFunctionWithDefaultFolds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package pk;\n"
      "  function automatic int twice(int a, int b = 2); return a * b;\n"
      "  endfunction\n"
      "endpackage\n"
      "module m;\n"
      "  import pk::*;\n"
      "  localparam int P = twice(6);\n"
      "  localparam int Q = pk::twice(7, 1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(ResolvedParam(design, "P"), 12);
  EXPECT_EQ(ResolvedParam(design, "Q"), 7);
}

// An explicit import names the one function it imports (§26.3): the other
// package function stays unreachable by its bare name, and the localparam
// naming it is left unresolved rather than folded.
TEST(ConstantFunctionElaboration, ExplicitImportBringsInTheNamedFunctionAlone) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package pk;\n"
      "  function automatic int twice(int a); return a * 2; endfunction\n"
      "  function automatic int thrice(int a); return a * 3; endfunction\n"
      "endpackage\n"
      "module m;\n"
      "  import pk::twice;\n"
      "  localparam int P = twice(5);\n"
      "  localparam int Q = thrice(5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(ResolvedParam(design, "P"), 10);
  EXPECT_EQ(ResolvedParam(design, "Q"), -1);
}

// §12.7.1 makes a variable a for loop's initialization declares a local of the
// implicit block around the loop, so in a constant function the loop's reads
// and writes of it name that local (#6411).
TEST(ConstantFunctionElaboration, ForLoopDeclaredVariableIsLocal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function automatic int f();\n"
      "    int s = 0;\n"
      "    for (int j = 0; j < 4; j++) s = s + j;\n"
      "    return s;\n"
      "  endfunction\n"
      "  localparam int P = f();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(design, "P"), 6);
}

// §11.2.1 makes a built-in method called on a constant identifier with
// constant arguments a constant built-in method call, which a constant
// function may make on a parameter as a localparam's initializer may (#6343).
TEST(ConstantFunctionElaboration, BuiltinMethodOnParameterAllowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam string S = \"abc\";\n"
      "  function automatic int f(); return S.len(); endfunction\n"
      "  localparam int P = f();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(design, "P"), 3);
}

// §13.4.3 excludes no case statement from a constant function's body, so one
// folds with §12.5's matching: case compares values exactly (#6375).
TEST(ConstantFunctionElaboration, CaseStatementFolds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function automatic int f(int s);\n"
      "    case (s) 0: return 8; 1, 2: return 6; default: return 4; endcase\n"
      "  endfunction\n"
      "  localparam int W = f(0);\n"
      "  localparam int X = f(2);\n"
      "  localparam int Y = f(5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(design, "W"), 8);
  EXPECT_EQ(ResolvedParam(design, "X"), 6);
  EXPECT_EQ(ResolvedParam(design, "Y"), 4);
}

// casez takes a z or ? bit of either side as matching anything (§12.5.1).
TEST(ConstantFunctionElaboration, CasezStatementFolds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function automatic int f(logic [3:0] s);\n"
      "    casez (s) 4'b1???: return 8; 4'b01??: return 6; default: return 4;\n"
      "    endcase\n"
      "  endfunction\n"
      "  localparam int W = f(4'b1010);\n"
      "  localparam int X = f(4'b0110);\n"
      "  localparam int Y = f(4'b0010);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(design, "W"), 8);
  EXPECT_EQ(ResolvedParam(design, "X"), 6);
  EXPECT_EQ(ResolvedParam(design, "Y"), 4);
}

// case inside matches a value against a range or a value (§12.5.4).
TEST(ConstantFunctionElaboration, CaseInsideStatementFolds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function automatic int f(int s);\n"
      "    case (s) inside [0:3]: return 8; 7, [10:12]: return 6;\n"
      "      default: return 4;\n"
      "    endcase\n"
      "  endfunction\n"
      "  localparam int W = f(2);\n"
      "  localparam int X = f(11);\n"
      "  localparam int Y = f(5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(design, "W"), 8);
  EXPECT_EQ(ResolvedParam(design, "X"), 6);
  EXPECT_EQ(ResolvedParam(design, "Y"), 4);
}

// §13.4.3 evaluates a constant function as it would run, so a real local and a
// real result keep their real values: x / 4 with x at 2.0 is 0.5, and 0.5
// times 4 is 2 (#6344).
TEST(ConstantFunctionElaboration, RealLocalsAndResultKeepTheirValues) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function automatic real f();\n"
      "    real x;\n"
      "    x++;\n"
      "    x++;\n"
      "    x++;\n"
      "    x--;\n"
      "    return x / 4;\n"
      "  endfunction\n"
      "  function automatic real g();\n"
      "    real y = 0.5;\n"
      "    y = y + 0.25;\n"
      "    return y;\n"
      "  endfunction\n"
      "  localparam int P = f() * 4;\n"
      "  localparam int Q = g() * 8;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(design, "P"), 2);
  EXPECT_EQ(ResolvedParam(design, "Q"), 6);
}

// casex takes an x bit of an item as matching anything as well (§12.5.1);
// case ignores none, and a constant selector holds no x or z, so an item with
// one matches nothing; a leftmost z digit fills the bits above it (§5.7.1),
// and a decimal literal's z digit every bit.
TEST(ConstantFunctionElaboration, CaseItemXAndZBitsFold) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function automatic int fx(logic [3:0] s);\n"
      "    casex (s) 4'b1x0?: return 8; default: return 4; endcase\n"
      "  endfunction\n"
      "  function automatic int fc(logic [3:0] s);\n"
      "    case (s) 4'b00x0: return 8; default: return 4; endcase\n"
      "  endfunction\n"
      "  function automatic int fz(logic [3:0] s);\n"
      "    casez (s) 4'bz1: return 8; default: return 4; endcase\n"
      "  endfunction\n"
      "  function automatic int fd(logic [3:0] s);\n"
      "    casez (s) 4'dz: return 8; default: return 4; endcase\n"
      "  endfunction\n"
      "  localparam int A = fx(4'b1101);\n"
      "  localparam int B = fx(4'b0101);\n"
      "  localparam int C = fc(4'b0000);\n"
      "  localparam int D = fz(4'b0101);\n"
      "  localparam int E = fz(4'b0100);\n"
      "  localparam int G = fd(4'b0110);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(design, "A"), 8);
  EXPECT_EQ(ResolvedParam(design, "B"), 4);
  EXPECT_EQ(ResolvedParam(design, "C"), 4);
  EXPECT_EQ(ResolvedParam(design, "D"), 8);
  EXPECT_EQ(ResolvedParam(design, "E"), 4);
  EXPECT_EQ(ResolvedParam(design, "G"), 8);
}

// An unsigned case inside range compares the values as unsigned (§12.5.4):
// 4'd3 is inside [4'd2:4'd5], and 4'd9 is not.
TEST(ConstantFunctionElaboration, UnsignedCaseInsideRangeFolds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function automatic int f(logic [3:0] s);\n"
      "    case (s) inside [4'd2:4'd5]: return 8; default: return 4; endcase\n"
      "  endfunction\n"
      "  localparam int W = f(4'd3);\n"
      "  localparam int X = f(4'd9);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(design, "W"), 8);
  EXPECT_EQ(ResolvedParam(design, "X"), 4);
}

// A formal declared real takes the real its actual is, and a real result read
// in an integral context is rounded (§6.12.1): h(1.25) is 2.5, which rounds
// to 3, and times 4 is 10.0.
TEST(ConstantFunctionElaboration, RealFormalKeepsItsValue) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function automatic real h(real a); return a * 2; endfunction\n"
      "  localparam int R = h(1.25) * 4;\n"
      "  localparam int S = h(1.25);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(design, "R"), 10);
  EXPECT_EQ(ResolvedParam(design, "S"), 3);
}

// §5.7.1's digits in every base: a hex item's letters and an underscore, an
// octal item, upper-case X and Z, a leftmost x filling the bits above it, a
// decimal x standing for every bit, and an item wider than 64 bits.
TEST(ConstantFunctionElaboration, CaseItemDigitsOfEveryBaseFold) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function automatic int fh(logic [7:0] s);\n"
      "    casez (s) 8'hA_Z: return 8; default: return 4; endcase\n"
      "  endfunction\n"
      "  function automatic int fo(logic [7:0] s);\n"
      "    casex (s) 8'o2X1: return 8; default: return 4; endcase\n"
      "  endfunction\n"
      "  function automatic int fl(logic [3:0] s);\n"
      "    casex (s) 4'bx0: return 8; default: return 4; endcase\n"
      "  endfunction\n"
      "  function automatic int fd(logic [3:0] s);\n"
      "    casex (s) 4'dx: return 8; default: return 4; endcase\n"
      "  endfunction\n"
      "  function automatic int fw(longint s);\n"
      "    casez (s)\n"
      "      128'h0000_0000_0000_0000_0000_0000_0000_00?1: return 8;\n"
      "      default: return 4;\n"
      "    endcase\n"
      "  endfunction\n"
      "  localparam int H1 = fh(8'hA7);\n"
      "  localparam int H2 = fh(8'hB7);\n"
      "  localparam int O1 = fo(8'hA9);\n"
      "  localparam int O2 = fo(8'hC1);\n"
      "  localparam int L1 = fl(4'b1110);\n"
      "  localparam int L2 = fl(4'b1111);\n"
      "  localparam int D1 = fd(4'b0110);\n"
      "  localparam int W1 = fw(64'h31);\n"
      "  localparam int W2 = fw(64'h30);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(design, "H1"), 8);
  EXPECT_EQ(ResolvedParam(design, "H2"), 4);
  EXPECT_EQ(ResolvedParam(design, "O1"), 8);
  EXPECT_EQ(ResolvedParam(design, "O2"), 4);
  EXPECT_EQ(ResolvedParam(design, "L1"), 8);
  EXPECT_EQ(ResolvedParam(design, "L2"), 4);
  EXPECT_EQ(ResolvedParam(design, "D1"), 8);
  EXPECT_EQ(ResolvedParam(design, "W1"), 8);
  EXPECT_EQ(ResolvedParam(design, "W2"), 4);
}

// A case statement whose selector, item or range bound does not fold leaves
// the call unfolded rather than choosing an arm: `bad` holds a forever loop,
// which the interpreter does not model.
TEST(ConstantFunctionElaboration, CaseWithAnUnfoldedOperandDoesNotFold) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function automatic int bad();\n"
      "    forever break;\n"
      "    return 1;\n"
      "  endfunction\n"
      "  function automatic int fs(int s);\n"
      "    case (bad()) 1: return 8; default: return 4; endcase\n"
      "  endfunction\n"
      "  function automatic int fi(int s);\n"
      "    case (s) bad(): return 8; default: return 4; endcase\n"
      "  endfunction\n"
      "  function automatic int fr(int s);\n"
      "    case (s) inside [0:bad()]: return 8; default: return 4; endcase\n"
      "  endfunction\n"
      "  localparam int S = fs(1);\n"
      "  localparam int I = fi(1);\n"
      "  localparam int R = fr(1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(ResolvedParam(design, "S"), -1);
  EXPECT_EQ(ResolvedParam(design, "I"), -1);
  EXPECT_EQ(ResolvedParam(design, "R"), -1);
}

// shortreal and realtime are real types (§6.12) as real is.
TEST(ConstantFunctionElaboration, ShortrealAndRealtimeKeepTheirValues) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function automatic realtime g(shortreal a);\n"
      "    realtime t = a;\n"
      "    return t * 3;\n"
      "  endfunction\n"
      "  localparam int Q = g(0.5) * 4;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(design, "Q"), 6);
}

// §11.3.1 applies the relational, equality and logical operators to reals, so
// a constant function's if, while and conditional predicates over a real fold
// by its value (#6422): each true test adds its bit, 919 in all.
TEST(ConstantFunctionElaboration, RealComparisonsFold) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function automatic int g();\n"
      "    real x = 1.5;\n"
      "    int n = 0;\n"
      "    if (x < 2.0) n = n + 1;\n"
      "    if (x <= 1.5) n = n + 2;\n"
      "    if (x > 1.0) n = n + 4;\n"
      "    if (x >= 2.0) n = n + 8;\n"
      "    if (x == 1.5) n = n + 16;\n"
      "    if (x != 1.5) n = n + 32;\n"
      "    if (x > 1.0 && x < 1.2) n = n + 64;\n"
      "    if (x < 1.0 || x > 1.2) n = n + 128;\n"
      "    if (!(x == 0.0)) n = n + 256;\n"
      "    while (x < 3.0) x = x + 0.5;\n"
      "    n = n + ((x == 3.0) ? 512 : 0);\n"
      "    return n;\n"
      "  endfunction\n"
      "  localparam int P = g();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(design, "P"), 919);
}

// §12.7.1 lets a for loop declare a real variable, which keeps its real value
// for the loop's run (#6423), and hands the name back afterwards to what it
// named outside: a real the loop hid, and an integer loop variable hiding a
// real.
TEST(ConstantFunctionElaboration, RealForLoopVariableKeepsItsValue) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function automatic int f1();\n"
      "    int n = 0;\n"
      "    for (real r = 0.5; r != 2.0; r = r + 0.5) n++;\n"
      "    return n;\n"
      "  endfunction\n"
      "  function automatic real f2();\n"
      "    real r = 9.5;\n"
      "    int n = 0;\n"
      "    for (real r = 0.5; r < 1.0; r = r + 0.25) n++;\n"
      "    return r + n;\n"
      "  endfunction\n"
      "  function automatic real f3();\n"
      "    real k = 1.5;\n"
      "    int n = 0;\n"
      "    for (int k = 0; k < 2; k++) n++;\n"
      "    return k + n;\n"
      "  endfunction\n"
      "  localparam int P1 = f1();\n"
      "  localparam int P2 = f2() * 2;\n"
      "  localparam int P3 = f3() * 2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(design, "P1"), 3);
  EXPECT_EQ(ResolvedParam(design, "P2"), 23);
  EXPECT_EQ(ResolvedParam(design, "P3"), 7);
}

// §13.4.3 ignores a constant function's system task calls, but not the
// elaboration severity tasks (§20.10.1), which report while the call is
// folded, formatted against the function's locals (#6434).
TEST(ConstantFunctionElaboration, SeverityTaskInBodyReportsWhileFolding) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function automatic int f(int n);\n"
      "    if (n > 3) $error(\"n is %0d, above 3\", n);\n"
      "    return n;\n"
      "  endfunction\n"
      "  localparam int P = f(5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "n is 5, above 3", 3, "20.10.1"));
}

// A call whose body never reaches the task reports nothing.
TEST(ConstantFunctionElaboration, SeverityTaskNotReachedReportsNothing) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function automatic int f(int n);\n"
      "    if (n > 3) $warning(\"n is %0d\", n);\n"
      "    return n;\n"
      "  endfunction\n"
      "  localparam int P = f(2);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
  EXPECT_EQ(ResolvedParam(design, "P"), 2);
}

// §13.4.3 bars a constant function from calling a constant function in any
// context requiring a constant expression, and a local parameter's
// initializer in its body is one (#6441); a constant there is not.
TEST(ConstantFunctionElaboration, ConstantCallInALocalParameterError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function automatic int g(int n); return n * 2; endfunction\n"
      "  function automatic int f(int n);\n"
      "    localparam int L = g(2);\n"
      "    return n + L;\n"
      "  endfunction\n"
      "  function automatic int h(int n);\n"
      "    localparam int L = 4;\n"
      "    return n + L;\n"
      "  endfunction\n"
      "  localparam int P = f(1);\n"
      "  localparam int Q = h(1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "constant function 'f' calls a function in a local "
                            "parameter's initializer",
                            11, "13.4.3"));
  EXPECT_EQ(ResolvedParam(design, "Q"), 5);
}

// Each of §20.10.1's severity tasks reports while a constant function folds,
// $fatal's first argument its finish number and $fatal and $error errors,
// $warning and $info warnings; any other system task is ignored (§13.4.3),
// and a call folded twice reports once.
TEST(ConstantFunctionElaboration, EverySeverityTaskReportsWhileFolding) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function automatic int f(int n);\n"
      "    if (n == 1) $fatal(1, \"fatal %0d\", n);\n"
      "    if (n == 2) $warning(\"warning %0d\", n);\n"
      "    if (n == 3) $info(\"info %0d\", n);\n"
      "    if (n == 4) $display(\"ignored %0d\", n);\n"
      "    if (n == 5) $error(\"error %0d\", n);\n"
      "    return n;\n"
      "  endfunction\n"
      "  localparam int A = f(1);\n"
      "  localparam int B = f(2);\n"
      "  localparam int C = f(3);\n"
      "  localparam int D = f(4);\n"
      "  localparam int E = f(5);\n"
      "  localparam int G = f(5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "elaboration FATAL: fatal 1",
                            3, "20.10.1"));
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "elaboration WARNING: warning 2", 4, "20.10.1"));
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(), "elaboration INFO: info 3",
                              5, "20.10.1"));
  int error5 = 0;
  for (const auto& d : f.diag.Diagnostics()) {
    if (d.message.find("error 5") != std::string::npos) ++error5;
    EXPECT_EQ(d.message.find("ignored"), std::string::npos);
  }
  EXPECT_EQ(error5, 1);
  EXPECT_EQ(ResolvedParam(design, "D"), 4);
}

}  // namespace
