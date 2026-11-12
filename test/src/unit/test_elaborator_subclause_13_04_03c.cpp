#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string>
#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

struct ParamValue {
  std::string_view name;
  int64_t value;
};

struct MarkedReport {
  std::string_view marker;
  std::string_view message;
};

int64_t ResolvedParam(RtlirDesign* design, std::string_view name) {
  if (!design || design->top_modules.empty()) return -1;
  for (const auto& p : design->top_modules[0]->params) {
    if (p.name == name) return p.is_resolved ? p.resolved_value : -1;
  }
  return -1;
}

void ExpectFolded(const std::string& src,
                  std::initializer_list<ParamValue> want) {
  ElabFixture f;
  auto* design = ElaborateSrc(src, f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  for (const auto& w : want) {
    EXPECT_EQ(ResolvedParam(design, w.name), w.value) << w.name;
  }
}

void ExpectReported(const std::string& src,
                    std::initializer_list<MarkedReport> want) {
  ElabFixture f;
  ElaborateSrc(src, f, "m");
  for (const auto& w : want) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), w.message,
                              LineHolding(src, w.marker), "13.4.3"));
  }
}

TEST(ConstantFunctionCallElaboration,
     DISABLED_AStaticClassMethodCallFoldsAsAConstantFunctionCall) {
  ExpectFolded(
      "class C;\n"
      "  static function int f(int a); return a * 2; endfunction\n"
      "endclass\n"
      "package pk;\n"
      "  class E;\n"
      "    static function int f(int a); return a + 10; endfunction\n"
      "  endclass\n"
      "endpackage\n"
      "class D #(parameter int W = 2);\n"
      "  static function int g(); return W + 1; endfunction\n"
      "endclass\n"
      "module m #(parameter int Q = C::f(4));\n"
      "  import pk::*;\n"
      "  class L;\n"
      "    static function int h(int a); return a * 5; endfunction\n"
      "  endclass\n"
      "  function int twice(int a); return a * 2; endfunction\n"
      "  localparam int P = C::f(3);\n"
      "  localparam int A = pk::E::f(1);\n"
      "  localparam int B = E::f(2);\n"
      "  localparam int H = L::h(2);\n"
      "  localparam int G1 = D#(5)::g();\n"
      "  localparam int G2 = D#()::g();\n"
      "  localparam int N = C::f(P + C::f(1));\n"
      "  localparam int T = C::f(twice(3));\n"
      "endmodule\n",
      {{"Q", 8},
       {"P", 6},
       {"A", 11},
       {"B", 12},
       {"H", 10},
       {"G1", 6},
       {"G2", 3},
       {"N", 16},
       {"T", 12}});
}

TEST(ConstantFunctionCallElaboration,
     DISABLED_AStaticClassMethodBreakingAConstraintIsReported) {
  ExpectReported(
      "class C;\n"
      "  static int s = 4;\n"
      "  static task t(); endtask\n"
      "  static function int r(); return s; endfunction\n"
      "  static function int o(int a, output int b); b = a; return a;\n"
      "  endfunction\n"
      "  static function int fk(int a); fork join_none return a; "
      "endfunction\n"
      "  static function int nc(int a); t(); return a; endfunction\n"
      "  static function int ok(int a); return a; endfunction\n"
      "  function int nf(); return 3; endfunction\n"
      "endclass\n"
      "module m;\n"
      "  int v, w;\n"
      "  localparam int R = C::r();\n"
      "  localparam int O = C::o(1, w);\n"
      "  localparam int F = C::fk(1);\n"
      "  localparam int N = C::nc(1);\n"
      "  localparam int A = C::ok(v);\n"
      "  localparam int NF = C::nf();\n"
      "endmodule\n",
      {{"int R =",
        "constant function 'r' references identifier 's' that is not a "
        "parameter, function name, or local declaration"},
       {"int O =",
        "constant function 'o' declares an argument of direction output, "
        "which constant functions are barred from"},
       {"int F =",
        "constant function 'fk' uses fork, which constant functions are "
        "barred from"},
       {"int N =",
        "constant function 'nc' invokes 't' which is not a constant "
        "function"},
       {"int A =", "constant function call 'ok' has a non-constant argument"},
       {"int NF =",
        "call of 'nf' is not a constant function call, since 'nf' is not a "
        "static method"}});
}

TEST(ConstantFunctionCallElaboration,
     AStaticClassMethodMeetingTheConstraintsIsNotReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  static function int ok(int a); return a; endfunction\n"
      "endclass\n"
      "module m;\n"
      "  localparam int K = C::ok(3);\n"
      "endmodule\n",
      f, "m");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConstantFunctionCallElaboration,
     DISABLED_APackageOrUnitParameterIsReadByAConstantFunction) {
  ExpectFolded(
      "package pk;\n"
      "  parameter int P = 5;\n"
      "  localparam int LP = 6;\n"
      "  parameter real R2 = 5.0;\n"
      "  parameter shortreal SR = 1.5;\n"
      "  parameter string S = \"abcd\";\n"
      "endpackage\n"
      "package pk2;\n"
      "  parameter int Q = 40;\n"
      "endpackage\n"
      "parameter int CU = 9;\n"
      "module m;\n"
      "  import pk::*;\n"
      "  import pk2::Q;\n"
      "  function automatic int f1(int x); return x + pk::P; endfunction\n"
      "  function automatic int f2(int x); return x + P; endfunction\n"
      "  function automatic int f3(int x); return x + $unit::CU; "
      "endfunction\n"
      "  function automatic int f4(int x); return x + CU; endfunction\n"
      "  function automatic int f5(int x); return x + LP; endfunction\n"
      "  function automatic int f6(int x); return x + Q; endfunction\n"
      "  function automatic int f7(int x);\n"
      "    return S.len() + (S == \"abcd\") * 10;\n"
      "  endfunction\n"
      "  function automatic int f8(int x);\n"
      "    return $rtoi(pk::R2 * 2) + $rtoi(pk::SR * 2) * 100;\n"
      "  endfunction\n"
      "  localparam int A1 = f1(1);\n"
      "  localparam int A2 = f2(2);\n"
      "  localparam int A3 = f3(1);\n"
      "  localparam int A4 = f4(2);\n"
      "  localparam int A5 = f5(1);\n"
      "  localparam int A6 = f6(1);\n"
      "  localparam int A7 = f7(1);\n"
      "  localparam int A8 = f8(1);\n"
      "endmodule\n",
      {{"A1", 6},
       {"A2", 7},
       {"A3", 10},
       {"A4", 11},
       {"A5", 7},
       {"A6", 41},
       {"A7", 14},
       {"A8", 310}});
}

TEST(ConstantFunctionCallElaboration,
     DISABLED_APackageParameterIsComputedInItsOwnScope) {
  ExpectFolded(
      "package pk;\n"
      "  parameter real R = 2.5;\n"
      "  parameter real R2 = R * 2;\n"
      "endpackage\n"
      "module m;\n"
      "  function automatic int f(real R); return $rtoi(pk::R2); "
      "endfunction\n"
      "  localparam int A = f(4.0);\n"
      "endmodule\n",
      {{"A", 5}});
}

TEST(ConstantFunctionCallElaboration,
     AnArgumentNamedLikeAnImportedParameterHidesIt) {
  ExpectFolded(
      "package pk;\n"
      "  parameter int P = 5;\n"
      "endpackage\n"
      "module m;\n"
      "  import pk::*;\n"
      "  function automatic int f(int P); return P * 3; endfunction\n"
      "  localparam int A = f(4);\n"
      "endmodule\n",
      {{"A", 12}});
}

TEST(ConstantFunctionCallElaboration,
     DISABLED_APackageOrUnitVariableInAConstantFunctionIsReported) {
  ExpectReported(
      "package pk;\n"
      "  int v;\n"
      "endpackage\n"
      "int cuv;\n"
      "module m;\n"
      "  int x;\n"
      "  function automatic int f1(int n); return n + pk::v; endfunction\n"
      "  function automatic int f2(int n); return n + cuv; endfunction\n"
      "  function automatic int f3(int n); return n + m.x; endfunction\n"
      "  localparam int A1 = f1(1);\n"
      "  localparam int A2 = f2(1);\n"
      "  localparam int A3 = f3(1);\n"
      "endmodule\n",
      {{"int A1 =",
        "constant function 'f1' references identifier 'v' that is not a "
        "parameter, function name, or local declaration"},
       {"int A2 =",
        "constant function 'f2' references identifier 'cuv' that is not a "
        "parameter, function name, or local declaration"},
       {"int A3 =",
        "constant function 'f3' uses a hierarchical reference, which "
        "constant functions are barred from"}});
}

TEST(ConstantFunctionCallElaboration,
     DISABLED_AStringMethodOnAnArgumentOrLocalFolds) {
  ExpectFolded(
      "module m;\n"
      "  function automatic int ma(string s);\n"
      "    return s.len() * 1000 + s.getc(1)\n"
      "        + (s.substr(1, 2) == \"bc\") * 100000;\n"
      "  endfunction\n"
      "  function automatic int ml(string s);\n"
      "    string t;\n"
      "    t = s;\n"
      "    return t.compare(\"abc\") + 10 * t.icompare(\"ABC\")\n"
      "        + 100 * (t.toupper() == \"ABC\")\n"
      "        + 1000 * (t.tolower() == \"abc\");\n"
      "  endfunction\n"
      "  function automatic int mn(string s);\n"
      "    string t;\n"
      "    t = s;\n"
      "    return t.atoi() + s.atohex() * 1000;\n"
      "  endfunction\n"
      "  localparam int A = ma(\"abc\");\n"
      "  localparam int B = ml(\"abc\");\n"
      "  localparam int C = mn(\"12\");\n"
      "endmodule\n",
      {{"A", 103098}, {"B", 1100}, {"C", 18012}});
}

TEST(ConstantFunctionCallElaboration,
     DISABLED_AStringOperatorOnAnArgumentOrLocalFolds) {
  ExpectFolded(
      "module m;\n"
      "  function automatic int ops(string s, string u);\n"
      "    string t;\n"
      "    t = {s, u, {2{u}}};\n"
      "    if (s == \"ab\")\n"
      "      return 1000 + (s != u) + 10 * (s < u) + 100 * (u > s)\n"
      "          + t.len() * 10000;\n"
      "    return 7;\n"
      "  endfunction\n"
      "  localparam int D = ops(\"ab\", \"cd\");\n"
      "  localparam int E = ops(\"zz\", \"cd\");\n"
      "endmodule\n",
      {{"D", 81111}, {"E", 7}});
}

TEST(ConstantFunctionCallElaboration,
     DISABLED_AStringBuiltInALoopOrDefaultedFolds) {
  ExpectFolded(
      "module m;\n"
      "  localparam string SP = \"Hey\";\n"
      "  function automatic int loop(int n);\n"
      "    string t;\n"
      "    t = \"\";\n"
      "    for (int i = 0; i < n; i++) t = {t, \"x\"};\n"
      "    return t.len();\n"
      "  endfunction\n"
      "  function automatic int dflt(string s = \"abcd\"); return s.len();\n"
      "  endfunction\n"
      "  localparam int E = loop(5);\n"
      "  localparam int F = dflt();\n"
      "  localparam int G = dflt(SP);\n"
      "endmodule\n",
      {{"E", 5}, {"F", 4}, {"G", 3}});
}

TEST(ConstantFunctionCallElaboration,
     DISABLED_AStringMethodOnAModuleVariableIsReportedBesideAnArgument) {
  std::string src =
      "module m;\n"
      "  string mv;\n"
      "  function automatic int g(); return mv.len(); endfunction\n"
      "  function automatic int g2(string s); return s.len(); endfunction\n"
      "  localparam int B = g();\n"
      "  localparam int B2 = g2(\"abc\");\n"
      "endmodule\n";
  ElabFixture f;
  ElaborateSrc(src, f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "constant function 'g' references identifier 'mv' "
                            "that is not a parameter, function name, or local "
                            "declaration",
                            LineHolding(src, "int B ="), "13.4.3"));
  EXPECT_FALSE(ErrorOnLine(f.diag.Diagnostics(), LineHolding(src, "int B2")));
}

TEST(ConstantFunctionCallElaboration,
     DISABLED_AQueueAssociativeOrDynamicArrayLocalFolds) {
  ExpectFolded(
      "module m;\n"
      "  function automatic int qf(int n);\n"
      "    int q[$];\n"
      "    for (int i = 0; i < n; i++) q.push_back(i);\n"
      "    return q.size() * 100 + q.sum();\n"
      "  endfunction\n"
      "  function automatic int af(int n);\n"
      "    int aa[int];\n"
      "    for (int i = 0; i < n; i++) aa[i * 3] = i;\n"
      "    return aa.num() + aa.exists(3) * 1000;\n"
      "  endfunction\n"
      "  function automatic int df(int n);\n"
      "    int d[];\n"
      "    d = new[n];\n"
      "    foreach (d[i]) d[i] = i;\n"
      "    return d.size() * 100 + d.sum();\n"
      "  endfunction\n"
      "  localparam int Q = qf(4);\n"
      "  localparam int A = af(4);\n"
      "  localparam int D = df(4);\n"
      "endmodule\n",
      {{"Q", 406}, {"A", 1004}, {"D", 406}});
}

TEST(ConstantFunctionCallElaboration,
     DISABLED_AConstantCallSizingALocalOfAConstantFunctionIsReported) {
  ExpectReported(
      "module m;\n"
      "  function automatic int g(int n); return n * 2; endfunction\n"
      "  function automatic int f3(int n);\n"
      "    logic [g(2)-1:0] v;\n"
      "    v = '1;\n"
      "    return v;\n"
      "  endfunction\n"
      "  function automatic int f5(int n);\n"
      "    int a [g(1)];\n"
      "    return $size(a);\n"
      "  endfunction\n"
      "  localparam int A3 = f3(1);\n"
      "  localparam int A5 = f5(1);\n"
      "endmodule\n",
      {{"int A3 =",
        "constant function 'f3' calls a function in a local declaration's "
        "dimension"},
       {"int A5 =",
        "constant function 'f5' calls a function in a local declaration's "
        "dimension"}});
}

TEST(ConstantFunctionCallElaboration,
     ALocalSizedByAParameterIsAcceptedInAConstantFunction) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  parameter int W = 3;\n"
      "  function automatic int f4(int n);\n"
      "    logic [W-1:0] v;\n"
      "    int a [W];\n"
      "    v = '1;\n"
      "    return v + $size(a);\n"
      "  endfunction\n"
      "  localparam int A4 = f4(1);\n"
      "endmodule\n",
      f, "m");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConstantFunctionCallElaboration,
     DISABLED_AParameterDeclaredAfterTheInvokingCallIsReported) {
  ExpectReported(
      "module m;\n"
      "  localparam int A = f(1);\n"
      "  localparam int AT = ft(1);\n"
      "  parameter int P = 4;\n"
      "  parameter type T = logic [3:0];\n"
      "  function automatic int f(int n); return n + P; endfunction\n"
      "  function automatic int ft(int n); return n + $bits(T); "
      "endfunction\n"
      "endmodule\n",
      {{"int A =",
        "constant function call 'f' uses parameter 'P', which is declared "
        "after the call"},
       {"int AT =",
        "constant function call 'ft' uses parameter 'T', which is declared "
        "after the call"}});
}

TEST(ConstantFunctionCallElaboration,
     AParameterDeclaredBeforeTheInvokingCallFolds) {
  ExpectFolded(
      "module m;\n"
      "  parameter int P = 4;\n"
      "  parameter type T = logic [3:0];\n"
      "  function automatic int f(int n); return n + P; endfunction\n"
      "  localparam int B = f(1);\n"
      "  localparam int BT = ft(2);\n"
      "  function automatic int ft(int n); return n + $bits(T); "
      "endfunction\n"
      "endmodule\n",
      {{"B", 5}, {"BT", 6}});
}

TEST(ConstantFunctionCallElaboration,
     DISABLED_AUnitFunctionCallFoldsAsAConstantFunctionCall) {
  ExpectFolded(
      "function automatic int uf(int n); return n * 7; endfunction\n"
      "module m;\n"
      "  localparam int U = uf(2);\n"
      "  localparam int U2 = $unit::uf(3);\n"
      "endmodule\n",
      {{"U", 14}, {"U2", 21}});
}

TEST(ConstantFunctionCallElaboration,
     DISABLED_AFunctionOfAnotherDesignElementIsNoConstantFunctionCall) {
  ExpectReported(
      "module other;\n"
      "  function automatic int of(int n); return n * 3; endfunction\n"
      "endmodule\n"
      "module m;\n"
      "  other o();\n"
      "  localparam int A = o.of(2);\n"
      "endmodule\n",
      {{"int A =",
        "call of 'o.of' is not a constant function call, since its function "
        "is declared in another design element"}});
}

TEST(ConstantFunctionCallElaboration,
     DISABLED_AConstantFunctionsLocalKeepsItsDeclaredType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m #(parameter type T = logic [4:0]);\n"
      "  parameter int W = 3;\n"
      "  function automatic int a1(); logic [2:0] v; v = '1; return v; "
      "endfunction\n"
      "  function automatic int a4(); logic [W-1:0] v; v = 15; return v; "
      "endfunction\n"
      "  function automatic int a5(); int a [3]; return $size(a); "
      "endfunction\n"
      "  function automatic int a6(); logic [W-1:0] v; return $bits(v); "
      "endfunction\n"
      "  function automatic int tv(); T v; v = '1; return v; endfunction\n"
      "  localparam int A1 = a1();\n"
      "  localparam int A4 = a4();\n"
      "  localparam int A5 = a5();\n"
      "  localparam int A6 = a6();\n"
      "  localparam int TV = tv();\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(design, "A1"), 7);
  EXPECT_EQ(ResolvedParam(design, "A4"), 7);
  EXPECT_EQ(ResolvedParam(design, "A5"), 3);
  EXPECT_EQ(ResolvedParam(design, "A6"), 3);
  EXPECT_EQ(ResolvedParam(design, "TV"), 31);
}

}  // namespace
