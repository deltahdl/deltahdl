#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <vector>

#include "common/diagnostic.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr const char* kTypeViaHandle = "via class handle";

bool ErrorOnLine(const std::vector<Diagnostic>& diags, uint32_t line) {
  for (const auto& d : diags) {
    if (d.severity == DiagSeverity::kError && d.loc.line == line) return true;
  }
  return false;
}

TEST(ObjectPropertyElaboration, ClassWithPropertiesElaborates) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  int command;\n"
             "  int address;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "endmodule\n"));
}

TEST(ObjectPropertyElaboration, VariousPropertyTypes) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int i;\n"
             "  real r;\n"
             "  string s;\n"
             "  bit [7:0] b;\n"
             "  logic [31:0] l;\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(ObjectPropertyElaboration, MultiplePropertyAccess) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  int header;\n"
             "  int payload;\n"
             "  int crc;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    automatic int x;\n"
             "    p.header = 1;\n"
             "    p.payload = 2;\n"
             "    p.crc = 3;\n"
             "    x = p.header;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ObjectPropertyElaboration, PropertyReadElaborates) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  int command;\n"
             "  int address;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    automatic int var1;\n"
             "    Packet p;\n"
             "    p = new;\n"
             "    p.command = 1;\n"
             "    p.address = 2;\n"
             "    var1 = p.command;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ObjectPropertyElaboration, EnumAccessViaInstanceElaborates) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  typedef enum {ERR_OVERFLOW = 10, ERR_UNDERFLOW = 1123} "
             "PCKT_TYPE;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Packet p;\n"
             "    automatic int x;\n"
             "    p = new;\n"
             "    x = p.ERR_OVERFLOW;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ObjectPropertyElaboration, ParameterValueAccessViaInstanceElaborates) {
  EXPECT_TRUE(
      ElabOk("class vector #(parameter width = 7, type T = int);\n"
             "  T data;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    automatic int w;\n"
             "    vector #(3) v;\n"
             "    v = new;\n"
             "    w = v.width;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ObjectPropertyElaboration, TypeParamAccessViaHandleIsIllegal) {
  ElabFixture f;
  ElabOk(
      "class vector #(parameter width = 7, type T = int);\n"
      "  T data;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    vector #(3) v;\n"
      "    v = new;\n"
      "    $display((v.T)'(3));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot access type parameter via class handle", 8,
                            "8.5"));
}

TEST(ObjectPropertyElaboration, InstanceParamAccessIsNotConstant) {
  ElabFixture f;
  ElabOk(
      "class vector #(parameter width = 7);\n"
      "  bit [width:0] data;\n"
      "endclass\n"
      "module m;\n"
      "  logic [31:0] bus;\n"
      "  logic [31:0] slice;\n"
      "  initial begin\n"
      "    vector #(3) v;\n"
      "    v = new;\n"
      "    slice = bus[0 +: v.width];\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "indexed part-select width must be a constant expression", 10, "11.5.1"));
}

TEST(ObjectPropertyElaboration, ConstantPartSelectWidthOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [31:0] bus;\n"
             "  logic [3:0] slice;\n"
             "  initial begin\n"
             "    slice = bus[0 +: 4];\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ObjectPropertyElaboration, TypeAccessViaScopeResolutionIsLegal) {
  EXPECT_TRUE(
      ElabOk("class vector #(parameter width = 7, type T = int);\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    $display(vector#(3)::T'(3));\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ObjectPropertyElaboration, EnumConstantsAndParametersAreMembers) {
  EXPECT_TRUE(
      ElabOk("class H; int v; endclass\n"
             "class C #(int W = 4);\n"
             "  typedef enum {RED, GREEN} color_t;\n"
             "  enum {UP, DOWN} dir;\n"
             "  localparam int L = 2;\n"
             "  H p = new;\n"
             "endclass\n"
             "module m;\n"
             "  C c = new;\n"
             "  initial $display(c.RED, c.UP, c.W, c.L, c.p.v, c.dir);\n"
             "endmodule\n"));
}

TEST(ObjectPropertyElaboration, UndeclaredMemberOfAnArrayElementIsReported) {
  ElabFixture f;
  ElabOk(
      "class H; int v; endclass\n"
      "module m;\n"
      "  H hs[];\n"
      "  initial begin\n"
      "    $display(hs.size());\n"
      "    hs[0].nosuch = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class 'H' has no member named 'nosuch'", 6,
                            "8.5"));
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), "has no member named", 5, "8.6"));
}

TEST(ObjectPropertyElaboration, TypesTheScopeDeclaresAreNotOuterClasses) {
  EXPECT_TRUE(
      ElabOk("class T; endclass\n"
             "class H; int v; endclass\n"
             "class C #(type T = H);\n"
             "  T p = new;\n"
             "endclass\n"
             "class N;\n"
             "  class Inner; int w; endclass\n"
             "  Inner i = new;\n"
             "  int q[$];\n"
             "  Inner is[$];\n"
             "endclass\n"
             "module m #(type T = H);\n"
             "  C c = new;\n"
             "  N n = new;\n"
             "  T t = new;\n"
             "  initial begin\n"
             "    t.v = 1;\n"
             "    $display(c.p.v, n.i.w, n.q.size(), n.is.size());\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ObjectPropertyElaboration, BaseThroughATypeParameterLeavesSelects) {
  ElabFixture f;
  ElabOk(
      "class B; int v; endclass\n"
      "class C #(type T = B) extends T;\n"
      "endclass\n"
      "module m;\n"
      "  C c = new;\n"
      "  initial c.v = 1;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), "has no member named", 6, "8.5"));
}

TEST(ObjectPropertyElaboration, BaseParameterNamedLikeAClassLeavesSelects) {
  ElabFixture f;
  ElabOk(
      "class T; endclass\n"
      "class B; int v; endclass\n"
      "class C #(type T = B) extends T;\n"
      "endclass\n"
      "module m;\n"
      "  C c = new;\n"
      "  initial c.v = 1;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), "has no member named", 7, "8.5"));
}

TEST(ObjectPropertyElaboration, NumberedEnumConstantsAreMembers) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  typedef enum {S[2], T[3:4], U[1]} s_t;\n"
      "endclass\n"
      "module m;\n"
      "  C c = new;\n"
      "  initial $display(c.S0, c.S1, c.T3, c.T4, c.U0);\n"
      "  initial $display(c.S2);\n"
      "  initial $display(c.S);\n"
      "  initial c.nosuch();\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_FALSE(ReportedError(diags, "has no member named", 6, "8.5"));
  EXPECT_TRUE(
      ReportedError(diags, "class 'C' has no member named 'S2'", 7, "8.5"));
  EXPECT_TRUE(
      ReportedError(diags, "class 'C' has no member named 'S'", 8, "8.5"));
  EXPECT_TRUE(
      ReportedError(diags, "class 'C' has no member named 'nosuch'", 9, "8.6"));
}

TEST(ObjectPropertyElaboration, ClassNameTwoScopesShareResolvesByScope) {
  ElabFixture f;
  ElabOk(
      "module a;\n"
      "  class K; int x; endclass\n"
      "endmodule\n"
      "module b;\n"
      "  class K; int y; endclass\n"
      "  class H; K k = new; endclass\n"
      "  class D extends K; endclass\n"
      "  H h = new;\n"
      "  D d = new;\n"
      "  initial h.k.y = 1;\n"
      "  initial d.y = 1;\n"
      "  initial h.k.x = 1;\n"
      "  initial d.x = 1;\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_FALSE(ReportedError(diags, "has no member named", 10, "8.5"));
  EXPECT_FALSE(ReportedError(diags, "has no member named", 11, "8.5"));
  EXPECT_TRUE(
      ReportedError(diags, "class 'K' has no member named 'x'", 12, "8.5"));
  EXPECT_TRUE(
      ReportedError(diags, "class 'D' has no member named 'x'", 13, "8.5"));
}

TEST(ObjectPropertyElaboration, SelectsFromNoHandleAreUnchecked) {
  EXPECT_TRUE(
      ElabOk("module child;\n"
             "  int v;\n"
             "endmodule\n"
             "module top;\n"
             "  child u();\n"
             "  string s = \"ab\";\n"
             "  initial $display(top.u.v, s.len());\n"
             "endmodule\n"));
}

TEST(ObjectPropertyElaboration,
     TypeReachedThroughAHandleIsReportedInEachPlace) {
  ElabFixture f;
  ElabOk(
      "class V #(parameter int W = 7, type T = int);\n"
      "  typedef byte b_t;\n"
      "  function void m(V #(3) o);\n"
      "    $display((o.T)'(3));\n"
      "  endfunction\n"
      "endclass\n"
      "function automatic void uf(V #(3) v);\n"
      "  $display((v.T)'(3));\n"
      "endfunction\n"
      "interface i;\n"
      "  V #(3) v;\n"
      "  initial $display((v.T)'(3));\n"
      "endinterface\n"
      "program p;\n"
      "  V #(3) v;\n"
      "  initial $display((v.T)'(3));\n"
      "endprogram\n"
      "module t;\n"
      "  i ui();\n"
      "  p up();\n"
      "  V #(3) v = new;\n"
      "  task tk;\n"
      "    $display((v.T)'(3));\n"
      "  endtask\n"
      "  initial begin\n"
      "    $display(V#(3)::T'(3));\n"
      "    $display(V#(3)::b_t'(3));\n"
      "  end\n"
      "endmodule\n"
      "package k;\n"
      "  function automatic void f(V #(3) v);\n"
      "    $display((v.T)'(3));\n"
      "  endfunction\n"
      "endpackage\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const uint32_t kLine : {4u, 8u, 12u, 16u, 23u, 32u}) {
    EXPECT_TRUE(ReportedError(diags, kTypeViaHandle, kLine, "8.5"));
  }
  for (const uint32_t kLine : {26u, 27u}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

TEST(ObjectPropertyElaboration,
     DISABLED_TypedefInheritedTypeOrPackageClassTypeViaHandle) {
  ElabFixture f;
  ElabOk(
      "class V #(parameter int W = 7, type T = int);\n"
      "  typedef byte b_t;\n"
      "endclass\n"
      "class D extends V #(4);\n"
      "endclass\n"
      "package k;\n"
      "  class PV #(type T = int); endclass\n"
      "  function automatic void f(PV v);\n"
      "    $display((v.T)'(3));\n"
      "  endfunction\n"
      "endpackage\n"
      "module t;\n"
      "  V #(3) v = new;\n"
      "  D d = new;\n"
      "  k::PV pv = new;\n"
      "  initial begin\n"
      "    $display((v.b_t)'(3));\n"
      "    $display((d.T)'(3));\n"
      "    $display((pv.T)'(3));\n"
      "    $display(D::b_t'(3));\n"
      "  end\n"
      "  if (1) begin : gb\n"
      "    V #(3) g;\n"
      "    initial $display((g.T)'(3));\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const uint32_t kLine : {9u, 17u, 18u, 19u, 24u}) {
    EXPECT_TRUE(ReportedError(diags, kTypeViaHandle, kLine, "8.5"));
  }
  EXPECT_FALSE(ErrorOnLine(diags, 20));
}

TEST(ObjectPropertyElaboration, ParameterReadThroughAHandleIsNotConstant) {
  ElabFixture f;
  ElabOk(
      "class V #(parameter int W = 7);\n"
      "  localparam int L = 5;\n"
      "endclass\n"
      "interface i;\n"
      "  V #(3) v;\n"
      "  localparam int A = v.W;\n"
      "  localparam int B = V#(3)::W;\n"
      "endinterface\n"
      "program p;\n"
      "  V #(3) v;\n"
      "  localparam int A = v.L;\n"
      "  localparam int B = V#(3)::L;\n"
      "endprogram\n"
      "module t;\n"
      "  i ui();\n"
      "  p up();\n"
      "  V #(3) v = new;\n"
      "  localparam int A = v.W;\n"
      "  localparam int B = V#(3)::W;\n"
      "  logic [31:0] bus, s;\n"
      "  initial begin\n"
      "    s = {v.W{1'b1}};\n"
      "    s = bus[0 +: v.L];\n"
      "    s = {V#(3)::W{1'b1}};\n"
      "    s = bus[0 +: V#(3)::L];\n"
      "  end\n"
      "  if (v.W > 2) begin : g1\n"
      "  end\n"
      "  if (V#(3)::W > 2) begin : g2\n"
      "    localparam int C = v.L;\n"
      "    localparam int D = V#(3)::L;\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(diags, "parameter 'A' value", 6, "6.20.2"));
  EXPECT_TRUE(ReportedError(diags, "parameter 'A' value", 11, "6.20.2"));
  EXPECT_TRUE(ReportedError(diags, "parameter 'A' value", 18, "6.20.2"));
  EXPECT_TRUE(ReportedError(
      diags, "replication multiplier shall be a constant expression", 22,
      "11.4.12.1"));
  EXPECT_TRUE(ReportedError(
      diags, "indexed part-select width must be a constant expression", 23,
      "11.5.1"));
  EXPECT_TRUE(ReportedError(diags, "generate-if condition is not constant", 27,
                            "27.5"));
  EXPECT_TRUE(ReportedError(diags, "parameter 'C' value", 30, "6.20.2"));
  for (const uint32_t kLine : {7u, 12u, 19u, 24u, 25u, 29u, 31u}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

TEST(ObjectPropertyElaboration,
     DISABLED_ParameterReadThroughAHandleIsNotConstantInSubroutinesAndBlocks) {
  ElabFixture f;
  ElabOk(
      "class V #(parameter int W = 7);\n"
      "  localparam int L = 5;\n"
      "endclass\n"
      "class U;\n"
      "  function void m(V #(3) o);\n"
      "    localparam int A = o.W;\n"
      "    localparam int B = V#(3)::W;\n"
      "  endfunction\n"
      "endclass\n"
      "package k;\n"
      "  function automatic void f(V #(3) o);\n"
      "    localparam int A = o.L;\n"
      "  endfunction\n"
      "endpackage\n"
      "function automatic void uf(V #(3) o);\n"
      "  localparam int A = o.W;\n"
      "endfunction\n"
      "module t;\n"
      "  V #(3) v = new;\n"
      "  task tk;\n"
      "    localparam int A = v.L;\n"
      "  endtask\n"
      "  initial begin\n"
      "    localparam int A = v.W;\n"
      "    localparam int B = V#(3)::L;\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const uint32_t kLine : {6u, 12u, 16u, 21u, 24u}) {
    EXPECT_TRUE(ReportedError(diags, "parameter 'A' value", kLine, "6.20.2"));
  }
  for (const uint32_t kLine : {7u, 25u}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

TEST(ObjectPropertyElaboration,
     DISABLED_ParameterReadThroughAHandleInAnInstanceOverrideIsReported) {
  ElabFixture f;
  ElabOk(
      "class V #(parameter int W = 7);\n"
      "endclass\n"
      "module sub #(parameter int P = 1);\n"
      "endmodule\n"
      "module t;\n"
      "  V #(3) v = new;\n"
      "  sub #(.P(v.W)) u1();\n"
      "  sub #(V#(3)::W) u2();\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(diags, "not a constant expression", 7, "23.10.2"));
  EXPECT_FALSE(ErrorOnLine(diags, 8));
}

}  // namespace
