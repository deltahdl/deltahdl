#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

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

}  // namespace
