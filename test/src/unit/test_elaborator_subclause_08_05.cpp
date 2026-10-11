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

// §8.5 forbids reaching a data type through a class handle and gives
// `$display ((v.T)'(3.45));` as its illegal example.
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

// §8.5 says of a parameter value read through an instance name that it is not a
// constant expression. The rule that rejects the source is §11.5.1's, which
// requires the width of an indexed part-select to be a constant expression, so
// the report names §11.5.1 rather than §8.5.
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

// The same part-select with a literal constant width is legal, isolating the
// rejection above to the non-constant instance-qualified access.
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

// §8.5: accessing a data type through a class handle is illegal, but naming a
// type through the class scope resolution operator on a specialization is legal
// typecasting - the accepting counterpart to TypeParamAccessViaHandleIsIllegal.
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

// §8.5 reaches a class's enumeration constants and value parameters through a
// handle as well as its properties, and a property holding a handle selects
// from its own class.
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

// An element of an array of handles, one select per unpacked dimension, is
// held to the class of its elements; the array itself, hs.size(), is not a
// handle.
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

// A type parameter of the class or of the module, or a class nested in the
// class, names no class of the scope around it, even where one bears its name;
// nor does a property of a type other than a class, or an array property
// selected as a whole, hold a handle.
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

// A class extending one known only through a type parameter has members the
// declaration does not show, so a select from it is left unreported, as it is
// where a class elsewhere bears the parameter's name.
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

// §6.19.2: a range of enumeration constants, S[2], T[3:4] or U[1], declares
// names the declaration does not write out, S0 and S1, T3 and T4, U0, which
// are members all the same; S2, the name that range stops short of, is not,
// and neither is the written S or a method no member names.
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

// A range bounded by a class parameter, V[W], generates names only a
// specialization tells, so a select from the class is left unreported.
TEST(ObjectPropertyElaboration, EnumRangeOverAParameterLeavesSelects) {
  ElabFixture f;
  ElabOk(
      "class C #(int W = 2);\n"
      "  typedef enum {V[W]} v_t;\n"
      "endclass\n"
      "module m;\n"
      "  C c = new;\n"
      "  initial $display(c.V1);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), "has no member named", 6, "8.5"));
}

// §3.13 and §23.9: a class name two scopes each declare a class under names,
// in a property's type and in an extends clause, the class the scope
// declaring the writer sees, so h.k and d hold b's K, which declares y and no
// x, whatever module a's K declares.
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

// A hierarchical name and a method of a built-in type select from no class
// handle.
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
