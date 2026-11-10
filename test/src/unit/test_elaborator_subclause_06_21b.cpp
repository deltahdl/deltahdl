#include <gtest/gtest.h>

#include <cstdint>
#include <format>
#include <initializer_list>
#include <string>
#include <string_view>
#include <utility>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(LifetimeIntentElaboration, InitializedLoopLocalInAnInitialReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top_illegal;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 3; i++) begin\n"
      "      int loop3 = 0;\n"
      "      for (int j = 0; j < 3; j++) begin\n"
      "        loop3++;\n"
      "        $display(loop3);\n"
      "      end\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'loop3' declared with an initializer in "
                            "a static block, task or function must be declared "
                            "static or automatic",
                            4, "6.21"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

TEST(LifetimeIntentElaboration, LoopLocalsWithAStatedLifetimeAccepted) {
  EXPECT_TRUE(
      ElabOk("module top_legal;\n"
             "  initial begin\n"
             "    for (int i = 0; i < 3; i++) begin\n"
             "      automatic int loop3 = 0;\n"
             "      loop3++;\n"
             "    end\n"
             "    for (int i = 0; i < 3; i++) begin\n"
             "      static int loop2 = 0;\n"
             "      loop2++;\n"
             "    end\n"
             "  end\n"
             "endmodule\n"));
}

TEST(LifetimeIntentElaboration, UninitializedLoopLocalAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  initial begin\n"
             "    repeat (3) begin\n"
             "      int n;\n"
             "      n = 1;\n"
             "    end\n"
             "  end\n"
             "endmodule\n"));
}

TEST(LifetimeIntentElaboration, InitializedLocalInAStaticTaskLoopReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  task tk;\n"
      "    while (1) begin\n"
      "      int k = 2;\n"
      "      break;\n"
      "    end\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'k' declared with an initializer in a "
                            "static block, task or function must be declared "
                            "static or automatic",
                            4, "6.21"));
}

TEST(LifetimeIntentElaboration,
     InitializedLoopLocalInAnAutomaticScopeAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  task automatic tk;\n"
             "    forever begin\n"
             "      int k = 2;\n"
             "      break;\n"
             "    end\n"
             "  endtask\n"
             "endmodule\n"));
  EXPECT_TRUE(
      ElabOk("module automatic m;\n"
             "  initial begin\n"
             "    do begin\n"
             "      int k = 2;\n"
             "    end while (0);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(LifetimeIntentElaboration, InitializedLocalAtTheTopOfAnInitialReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top_illegal;\n"
      "  initial begin\n"
      "    int svar2 = 2;\n"
      "    $display(svar2);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'svar2' declared with an initializer in "
                            "a static block, task or function must be declared "
                            "static or automatic",
                            3, "6.21"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

TEST(LifetimeIntentElaboration, TopLevelLocalsWithAStatedLifetimeAccepted) {
  EXPECT_TRUE(
      ElabOk("module top_legal;\n"
             "  initial begin\n"
             "    static int svar1 = 1;\n"
             "    automatic int avar1 = 1;\n"
             "    $display(svar1, avar1);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(LifetimeIntentElaboration, BlockParameterWithAValueAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  initial begin\n"
             "    localparam int W = 4;\n"
             "    parameter int D = 2;\n"
             "    $display(W, D);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(LifetimeIntentElaboration, InitializedLocalsInAutomaticScopesAccepted) {
  EXPECT_TRUE(
      ElabOk("module automatic m;\n"
             "  initial begin\n"
             "    int n = 1;\n"
             "    $display(n);\n"
             "  end\n"
             "endmodule\n"));
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  task automatic tk;\n"
             "    int n = 1;\n"
             "    $display(n);\n"
             "  endtask\n"
             "endmodule\n"));
}

TEST(LifetimeIntentElaboration,
     InitializedLocalInARandsequenceCodeBlockAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int av;\n"
             "  initial begin\n"
             "    randsequence(main)\n"
             "      main : { int fresh = 0; fresh++; av = fresh; } ;\n"
             "    endsequence\n"
             "  end\n"
             "endmodule\n"));
}

TEST(LifetimeIntentElaboration, InitializedLocalInAStaticFunctionReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  function int f();\n"
      "    int n = 1;\n"
      "    return n;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'n' declared with an initializer in a "
                            "static block, task or function must be declared "
                            "static or automatic",
                            3, "6.21"));
}

TEST(LifetimeIntentElaboration, InitializedLocalInAClassMethodAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  function int f();\n"
             "    int n = 1;\n"
             "    return n;\n"
             "  endfunction\n"
             "  extern function int g();\n"
             "endclass\n"
             "function int C::g();\n"
             "  int n = 2;\n"
             "  return n;\n"
             "endfunction\n"
             "module t;\n"
             "  initial begin\n"
             "    static C c = new;\n"
             "    $display(c.f(), c.g());\n"
             "  end\n"
             "endmodule\n"));
}

TEST(LifetimeIntentElaboration, InitializedLocalInAGenerateIfBlockReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  if (1) begin : g\n"
      "    initial begin\n"
      "      int x = 1;\n"
      "      $display(x);\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'x' declared with an initializer in a "
                            "static block, task or function must be declared "
                            "static or automatic",
                            4, "6.21"));
}

TEST(LifetimeIntentElaboration, GenerateBlockLocalsWithALifetimeAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  if (1) begin : g\n"
             "    initial begin\n"
             "      static int x = 1;\n"
             "      $display(x);\n"
             "    end\n"
             "  end\n"
             "endmodule\n"));
  EXPECT_TRUE(
      ElabOk("module automatic m;\n"
             "  if (1) begin : g\n"
             "    initial begin\n"
             "      int x = 1;\n"
             "      $display(x);\n"
             "    end\n"
             "  end\n"
             "endmodule\n"));
}

TEST(LifetimeIntentElaboration, InitializedLocalInAGenerateForTaskReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  for (genvar i = 0; i < 2; i++) begin : g\n"
      "    task tk;\n"
      "      int n = 1;\n"
      "      $display(n);\n"
      "    endtask\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'n' declared with an initializer in a "
                            "static block, task or function must be declared "
                            "static or automatic",
                            4, "6.21"));
}

TEST(LifetimeIntentElaboration, InitializedLocalsInElseAndCaseArmsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  if (0) begin : a\n"
      "  end else begin : b\n"
      "    initial begin\n"
      "      int e = 1;\n"
      "    end\n"
      "  end\n"
      "  case (1)\n"
      "    1: begin : c\n"
      "      initial begin\n"
      "        int k = 1;\n"
      "      end\n"
      "    end\n"
      "  endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'e' declared with an initializer in a "
                            "static block, task or function must be declared "
                            "static or automatic",
                            5, "6.21"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'k' declared with an initializer in a "
                            "static block, task or function must be declared "
                            "static or automatic",
                            11, "6.21"));
}

TEST(LifetimeIntentElaboration, InitializedLocalInAPackageFunctionReported) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  function int f();\n"
      "    int n = 1;\n"
      "    return n;\n"
      "  endfunction\n"
      "endpackage\n"
      "module t;\n"
      "  initial $display(p::f());\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'n' declared with an initializer in a "
                            "static block, task or function must be declared "
                            "static or automatic",
                            3, "6.21"));
}

TEST(LifetimeIntentElaboration, PackageLocalsWithALifetimeAccepted) {
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  function int f();\n"
             "    static int s = 1;\n"
             "    automatic int a = 1;\n"
             "    return s + a;\n"
             "  endfunction\n"
             "endpackage\n"));
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  function automatic int f();\n"
             "    int n = 1;\n"
             "    return n;\n"
             "  endfunction\n"
             "endpackage\n"));
  EXPECT_TRUE(
      ElabOk("package automatic p;\n"
             "  task tk;\n"
             "    int n = 1;\n"
             "    $display(n);\n"
             "  endtask\n"
             "endpackage\n"));
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  class C;\n"
             "    function int f();\n"
             "      int n = 1;\n"
             "      return n;\n"
             "    endfunction\n"
             "  endclass\n"
             "endpackage\n"));
}

TEST(LifetimeIntentElaboration, GenerateBlockAutoVarNonblockingReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  if (1) begin : g\n"
      "    initial begin\n"
      "      automatic int a;\n"
      "      a <= 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "automatic variable in nonblocking assignment", 5,
                            "6.21"));
}

TEST(LifetimeIntentElaboration, GenerateForAutoVarProcContAssignsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  for (genvar i = 0; i < 1; i++) begin : g\n"
      "    initial begin\n"
      "      automatic int a;\n"
      "      assign a = 1;\n"
      "      force a = 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "automatic block variable in procedural continuous "
                            "assignment",
                            5, "6.21"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "automatic block variable in procedural continuous "
                            "assignment",
                            6, "6.21"));
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  for (genvar i = 0; i < 1; i++) begin : g\n"
             "    initial begin\n"
             "      automatic int a;\n"
             "      a = 1;\n"
             "    end\n"
             "  end\n"
             "endmodule\n"));
}

TEST(LifetimeElaboration, ContinuousWriteOfANonStaticPropertyRejected) {
  ElabFixture f;
  Elaborate(
      "module top;\n"
      "  typedef struct {bit f;} st_t;\n"
      "  class C;\n"
      "    bit x;\n"
      "    bit [1:0] v;\n"
      "    st_t p;\n"
      "    static bit s;\n"
      "  endclass\n"
      "  C h = new;\n"
      "  st_t st;\n"
      "  bit y;\n"
      "  assign h.x = 1'b1;\n"
      "  assign st.f = 1'b0;\n"
      "  initial begin\n"
      "    assign h.v[0] = 1'b0;\n"
      "    force {h.x, y} = 2'b10;\n"
      "    force h.p.f = 1'b1;\n"
      "    force h.s = 1'b1;\n"
      "    force C::s = 1'b1;\n"
      "    force h.nosuch = 1'b1;\n"
      "  end\n"
      "  task automatic t();\n"
      "    force h.x = 1'b1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  const std::pair<uint32_t, std::string_view> kWrites[] = {
      {12, "h.x"}, {15, "h.v"}, {16, "h.x"}, {17, "h.p"}, {23, "h.x"}};
  for (const auto& [line, target] : kWrites) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        std::format("'{}' is a non-static class property, which no "
                    "continuous or procedural continuous assignment may write",
                    target),
        line, "6.21"));
  }
  for (uint32_t line : {13U, 18U, 19U, 20U}) {
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                               "is a non-static class property", line, "6.21"));
  }
}

constexpr std::string_view kContinuousDynamicWrite =
    "continuous assignment to element of dynamically sized array";
constexpr std::string_view kDynamicReadOutsideAProcedure =
    "element of dynamically sized array referenced outside a procedural block";

void ExpectReportedOnEachLine(const std::string& src, std::string_view message,
                              std::initializer_list<std::string_view> needles) {
  ElabFixture f;
  ElaborateSrc(src, f);
  for (std::string_view needle : needles) {
    SCOPED_TRACE(needle);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message,
                              LineHolding(src, needle), "6.21"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), needles.size());
}

TEST(DynamicElementLifetime,
     DISABLED_ContinuousWriteOfADynamicArrayElementReported) {
  ExpectReportedOnEachLine(
      "module top;\n"
      "  int d[];\n"
      "  int q[$];\n"
      "  int a[string];\n"
      "  int f[2];\n"
      "  int x;\n"
      "  assign d[0] = x;\n"
      "  assign q[1] = x;\n"
      "  assign a[\"k\"] = x;\n"
      "  assign f[0] = x;\n"
      "endmodule\n",
      kContinuousDynamicWrite, {"d[0] = x", "q[1] = x", "a[\"k\"] = x"});
}

TEST(DynamicElementLifetime,
     DISABLED_ContinuousWriteOfAPartOrMemberOfADynamicElementReported) {
  ExpectReportedOnEachLine(
      "module top;\n"
      "  typedef struct {int f;} s_t;\n"
      "  int d[];\n"
      "  s_t s[];\n"
      "  int x, y, z;\n"
      "  assign d[0][3:0] = x;\n"
      "  assign s[0].f = x;\n"
      "  assign {d[1], y} = z;\n"
      "endmodule\n",
      kContinuousDynamicWrite, {"d[0][3:0]", "s[0].f", "{d[1], y}"});
}

TEST(DynamicElementLifetime,
     DISABLED_GateAndPortOutputOnADynamicElementReported) {
  ExpectReportedOnEachLine(
      "module child(input var int i, output int o);\n"
      "endmodule\n"
      "module top;\n"
      "  int d[];\n"
      "  int x;\n"
      "  logic l;\n"
      "  buf (d[0], l);\n"
      "  child c(.i(x), .o(d[1]));\n"
      "endmodule\n",
      kContinuousDynamicWrite, {"buf (d[0]", ".o(d[1])"});
}

TEST(DynamicElementLifetime,
     DISABLED_ContinuousWriteOfADynamicElementReportedInEveryScope) {
  ExpectReportedOnEachLine(
      "interface ifc;\n"
      "  int d[];\n"
      "  int x;\n"
      "  assign d[0] = x;\n"
      "endinterface\n"
      "program prg;\n"
      "  int q[$];\n"
      "  int x;\n"
      "  assign q[0] = x;\n"
      "endprogram\n"
      "module top;\n"
      "  ifc i();\n"
      "  prg p();\n"
      "  for (genvar g = 0; g < 1; g++) begin : gb\n"
      "    int a[int];\n"
      "    int x;\n"
      "    assign a[0] = x;\n"
      "  end\n"
      "endmodule\n",
      kContinuousDynamicWrite, {"d[0] = x", "q[0] = x", "a[0] = x"});
}

TEST(DynamicElementLifetime, FixedArrayElementContinuousWritesAccepted) {
  EXPECT_TRUE(
      ElabOk("module child(input var int i, output int o);\n"
             "endmodule\n"
             "module top;\n"
             "  typedef struct {int f;} s_t;\n"
             "  int f[4];\n"
             "  s_t s[1];\n"
             "  logic g[2];\n"
             "  int x, y, z;\n"
             "  logic l;\n"
             "  assign f[0] = x;\n"
             "  assign f[1][3:0] = x;\n"
             "  assign s[0].f = x;\n"
             "  assign {f[2], y} = z;\n"
             "  buf (g[0], l);\n"
             "  child c(.i(x), .o(f[3]));\n"
             "endmodule\n"));
}

TEST(DynamicElementLifetime,
     DISABLED_DynamicElementReadOutsideAProcedureReported) {
  ExpectReportedOnEachLine(
      "module top;\n"
      "  int d[];\n"
      "  int q[$];\n"
      "  int a[string];\n"
      "  int w1, w2, w3;\n"
      "  assign w1 = d[0];\n"
      "  assign w2 = q[$];\n"
      "  assign w3 = a[\"k\"];\n"
      "endmodule\n",
      kDynamicReadOutsideAProcedure, {"= d[0]", "= q[$]", "= a[\"k\"]"});
}

TEST(DynamicElementLifetime,
     DISABLED_DynamicElementAsAGateInputPortOrDelayReported) {
  ExpectReportedOnEachLine(
      "module child(input var int i, output int o);\n"
      "endmodule\n"
      "module top;\n"
      "  logic d[];\n"
      "  int e[];\n"
      "  int w, x, o1;\n"
      "  logic o;\n"
      "  buf (o, d[0]);\n"
      "  child c(.i(e[0]), .o(o1));\n"
      "  assign #(e[1]) w = x;\n"
      "endmodule\n",
      kDynamicReadOutsideAProcedure, {"buf (o", ".i(e[0])", "#(e[1])"});
}

TEST(DynamicElementLifetime,
     DISABLED_ClassMemberReadOutsideAProcedureReported) {
  ElabFixture f;
  std::string src =
      "class K;\n"
      "  int v;\n"
      "endclass\n"
      "module top;\n"
      "  K h = new;\n"
      "  int w;\n"
      "  assign w = h.v;\n"
      "endmodule\n";
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "member of a class object referenced outside a procedural block",
      LineHolding(src, "h.v"), "6.21"));
}

TEST(DynamicElementLifetime, DynamicReadsInProceduresAccepted) {
  EXPECT_TRUE(
      ElabOk("class K;\n"
             "  int v;\n"
             "endclass\n"
             "module top;\n"
             "  int d[];\n"
             "  int q[$];\n"
             "  int a[string];\n"
             "  K h = new;\n"
             "  int w, n;\n"
             "  function int pick();\n"
             "    return d[0] + q[$] + a[\"k\"] + h.v;\n"
             "  endfunction\n"
             "  always @* w = d[0] + q[$] + a[\"k\"] + h.v;\n"
             "  always @* n = pick();\n"
             "  final $display(d[0], q[$], a[\"k\"], h.v);\n"
             "endmodule\n"));
}

TEST(HierarchicalLifetime, DISABLED_PathToAnAutomaticLocalReported) {
  ExpectReportedOnEachLine(
      "module top;\n"
      "  task automatic ta;\n"
      "    int a;\n"
      "    a = 1;\n"
      "  endtask\n"
      "  function automatic int fa;\n"
      "    int v;\n"
      "    v = 2;\n"
      "    return v;\n"
      "  endfunction\n"
      "  task ts;\n"
      "    automatic int y;\n"
      "    y = 3;\n"
      "  endtask\n"
      "  initial $display(ta.a);\n"
      "  initial $display(fa.v);\n"
      "  initial $display(ts.y);\n"
      "endmodule\n",
      "automatic variable", {"ta.a", "fa.v", "ts.y"});
}

TEST(HierarchicalLifetime, DISABLED_PathIntoAnUnnamedBlockReported) {
  ExpectReportedOnEachLine(
      "module top;\n"
      "  initial begin : n\n"
      "    begin\n"
      "      static int x = 1;\n"
      "    end\n"
      "  end\n"
      "  task t;\n"
      "    begin\n"
      "      static int y;\n"
      "      y = 1;\n"
      "    end\n"
      "  endtask\n"
      "  initial #1 $display(n.x);\n"
      "  initial #1 $display(t.y);\n"
      "endmodule\n",
      "unnamed block", {"n.x", "t.y"});
}

TEST(HierarchicalLifetime, PathsToStaticLocalsAccepted) {
  EXPECT_TRUE(
      ElabOk("module top;\n"
             "  initial begin : n\n"
             "    begin : inner\n"
             "      static int x = 1;\n"
             "    end\n"
             "  end\n"
             "  task automatic ta;\n"
             "    static int s;\n"
             "    s++;\n"
             "  endtask\n"
             "  task t;\n"
             "    int y;\n"
             "    y = 1;\n"
             "  endtask\n"
             "  initial #1 $display(n.inner.x, ta.s, t.y);\n"
             "endmodule\n"));
}

TEST(LoopAndMethodLifetime,
     NonblockingWriteOfAnAutomaticByDefaultLocalReported) {
  ElabFixture f;
  std::string src =
      "class C;\n"
      "  task m;\n"
      "    int c;\n"
      "    c <= 1;\n"
      "  endtask\n"
      "endclass\n"
      "module top;\n"
      "  task t;\n"
      "    for (int j = 0; j < 1; j++) j <= 1;\n"
      "  endtask\n"
      "  initial begin\n"
      "    for (int i = 0; i < 1; i++) i <= 1;\n"
      "  end\n"
      "endmodule\n";
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "automatic task variable in nonblocking assignment",
                            LineHolding(src, "c <= 1"), "13.3.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "automatic variable in nonblocking assignment",
                            LineHolding(src, "j <= 1"), "6.21"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "automatic variable in nonblocking assignment",
                            LineHolding(src, "i <= 1"), "6.21"));
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  static int c;\n"
             "  task m;\n"
             "    c <= 1;\n"
             "  endtask\n"
             "endclass\n"
             "module top;\n"
             "  int i;\n"
             "  initial for (i = 0; i < 1; i++) i <= 1;\n"
             "endmodule\n"));
}

TEST(LifetimeIntentElaboration,
     InitializedLocalsInInterfaceAndProgramReported) {
  ExpectReportedOnEachLine(
      "interface ifc;\n"
      "  initial begin\n"
      "    int x = 1;\n"
      "  end\n"
      "endinterface\n"
      "program prg;\n"
      "  initial begin\n"
      "    int y = 1;\n"
      "  end\n"
      "  task t;\n"
      "    int z = 2;\n"
      "  endtask\n"
      "endprogram\n"
      "module top;\n"
      "  ifc i();\n"
      "  prg p();\n"
      "endmodule\n",
      "declared with an initializer in a static block, task or function",
      {"int x", "int y", "int z"});
  EXPECT_TRUE(
      ElabOk("interface automatic ifc;\n"
             "  initial begin\n"
             "    int x = 1;\n"
             "  end\n"
             "endinterface\n"
             "program automatic prg;\n"
             "  initial begin\n"
             "    int y = 1;\n"
             "  end\n"
             "  task t;\n"
             "    int z = 2;\n"
             "  endtask\n"
             "endprogram\n"
             "module top;\n"
             "  ifc i();\n"
             "  prg p();\n"
             "endmodule\n"));
}

}  // namespace
