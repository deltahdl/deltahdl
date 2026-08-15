

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(InterfaceClassDiamondInheritance, DiamondInheritanceOk) {
  EXPECT_TRUE(
      ElabOk("interface class IntfBase;\n"
             "  pure virtual function bit funcBase();\n"
             "endclass\n"
             "interface class IntfExt1 extends IntfBase;\n"
             "  pure virtual function bit funcExt1();\n"
             "endclass\n"
             "interface class IntfExt2 extends IntfBase;\n"
             "  pure virtual function bit funcExt2();\n"
             "endclass\n"
             "interface class IntfExt3 extends IntfExt1, IntfExt2;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassDiamond, ClassImplementsDiamondOk) {
  EXPECT_TRUE(
      ElabOk("interface class IntfBase;\n"
             "  pure virtual function bit funcBase();\n"
             "endclass\n"
             "interface class IntfExt1 extends IntfBase;\n"
             "  pure virtual function bit funcExt1();\n"
             "endclass\n"
             "interface class IntfExt2 extends IntfBase;\n"
             "  pure virtual function bit funcExt2();\n"
             "endclass\n"
             "class C implements IntfExt1, IntfExt2;\n"
             "  virtual function bit funcBase();\n"
             "    return 0;\n"
             "  endfunction\n"
             "  virtual function bit funcExt1();\n"
             "    return 0;\n"
             "  endfunction\n"
             "  virtual function bit funcExt2();\n"
             "    return 0;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassDiamondInheritance, DiamondParameterMergesOneCopy) {
  EXPECT_TRUE(
      ElabOk("interface class IntfBase;\n"
             "  parameter SIZE = 64;\n"
             "endclass\n"
             "interface class IntfExt1 extends IntfBase;\n"
             "  pure virtual function bit funcExt1();\n"
             "endclass\n"
             "interface class IntfExt2 extends IntfBase;\n"
             "  pure virtual function bit funcExt2();\n"
             "endclass\n"
             "interface class IntfExt3 extends IntfExt1, IntfExt2;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassDiamondInheritance, DiamondTypedefMergesOneCopy) {
  EXPECT_TRUE(
      ElabOk("interface class IntfBase;\n"
             "  typedef bit [7:0] byte_t;\n"
             "endclass\n"
             "interface class IntfExt1 extends IntfBase;\n"
             "  pure virtual function bit funcExt1();\n"
             "endclass\n"
             "interface class IntfExt2 extends IntfBase;\n"
             "  pure virtual function bit funcExt2();\n"
             "endclass\n"
             "interface class IntfExt3 extends IntfExt1, IntfExt2;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassDiamondInheritance, ThreePathDiamondMergesOneCopy) {
  EXPECT_TRUE(
      ElabOk("interface class IntfBase;\n"
             "  parameter SIZE = 64;\n"
             "  pure virtual function bit funcBase();\n"
             "endclass\n"
             "interface class IntfA extends IntfBase;\n"
             "  pure virtual function bit funcA();\n"
             "endclass\n"
             "interface class IntfB extends IntfBase;\n"
             "  pure virtual function bit funcB();\n"
             "endclass\n"
             "interface class IntfC extends IntfBase;\n"
             "  pure virtual function bit funcC();\n"
             "endclass\n"
             "interface class IntfAll extends IntfA, IntfB, IntfC;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// §8.26.6.3 states "There is no diamond relationship if different
// specializations of the same parameterized interface class are inherited by
// the same interface class ... As a result, method name conflicts as described
// in 8.26.6.1 and parameter and type declaration name conflicts as described in
// 8.26.6.2 may occur." §8.26.6.3 therefore names §8.26.6.2 as the rule the
// unresolved parameter T breaks, and the report carries that number.
TEST(InterfaceClassDiamond, DifferentSpecializationsNotDiamondError) {
  ElabFixture f;
  ElabOk(
      "interface class IntfBase #(type T = int);\n"
      "  pure virtual function bit funcBase();\n"
      "endclass\n"
      "interface class IntfExt1 extends IntfBase#(bit);\n"
      "  pure virtual function bit funcExt1();\n"
      "endclass\n"
      "interface class IntfExt2 extends IntfBase#(logic);\n"
      "  pure virtual function bit funcExt2();\n"
      "endclass\n"
      "interface class IntfFinal extends IntfExt1, IntfExt2;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "is inherited from multiple interface classes and must be overridden", 10,
      "8.26.6.2"));
}

TEST(InterfaceClassDiamond, DifferentSpecializationsWithOverrideOk) {
  EXPECT_TRUE(
      ElabOk("interface class IntfBase #(type T = int);\n"
             "  pure virtual function bit funcBase();\n"
             "endclass\n"
             "interface class IntfExt1 extends IntfBase#(bit);\n"
             "  pure virtual function bit funcExt1();\n"
             "endclass\n"
             "interface class IntfExt2 extends IntfBase#(logic);\n"
             "  pure virtual function bit funcExt2();\n"
             "endclass\n"
             "interface class IntfFinal extends IntfExt1, IntfExt2;\n"
             "  typedef bit T;\n"
             "  pure virtual function bit funcBase();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// Boundary of the specialization rule: identical parameterizations of a
// parameterized base reached through two paths denote the same interface
// class type, so they still form a diamond and merge to a single copy
// rather than colliding. Mirror of DifferentSpecializationsNotDiamondError
// with matching #(bit) arguments on both branches.
TEST(InterfaceClassDiamond, SameSpecializationIsDiamondMergesOneCopy) {
  EXPECT_TRUE(
      ElabOk("interface class IntfBase #(type T = int);\n"
             "  pure virtual function bit funcBase();\n"
             "endclass\n"
             "interface class IntfExt1 extends IntfBase#(bit);\n"
             "  pure virtual function bit funcExt1();\n"
             "endclass\n"
             "interface class IntfExt2 extends IntfBase#(bit);\n"
             "  pure virtual function bit funcExt2();\n"
             "endclass\n"
             "interface class IntfFinal extends IntfExt1, IntfExt2;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// The specialization rule is not confined to type parameters: distinct value
// parameterizations of a parameterized interface class are likewise distinct
// interface class types (§8.26.6.3). Reaching such a base through two paths
// with different value arguments is therefore not a diamond, so the parameter
// SIZE inherited from IntfBase#(1) and IntfBase#(2) collides and must be
// resolved. Value-arg counterpart of DifferentSpecializationsNotDiamondError.
TEST(InterfaceClassDiamond, DifferentValueSpecializationsNotDiamondError) {
  ElabFixture f;
  ElabOk(
      "interface class IntfBase #(int P = 1);\n"
      "  parameter SIZE = 8;\n"
      "endclass\n"
      "interface class IntfExt1 extends IntfBase#(1);\n"
      "  pure virtual function bit funcExt1();\n"
      "endclass\n"
      "interface class IntfExt2 extends IntfBase#(2);\n"
      "  pure virtual function bit funcExt2();\n"
      "endclass\n"
      "interface class IntfFinal extends IntfExt1, IntfExt2;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "is inherited from multiple interface classes and must be overridden", 10,
      "8.26.6.2"));
}

// Boundary of the value-specialization rule: identical value parameterizations
// reached through two paths denote the same interface class type, so they still
// form a diamond and the shared parameter merges to one copy rather than
// colliding. Value-arg counterpart of SameSpecializationIsDiamondMergesOneCopy.
TEST(InterfaceClassDiamond, SameValueSpecializationIsDiamondMergesOneCopy) {
  EXPECT_TRUE(
      ElabOk("interface class IntfBase #(int P = 1);\n"
             "  parameter SIZE = 8;\n"
             "endclass\n"
             "interface class IntfExt1 extends IntfBase#(1);\n"
             "  pure virtual function bit funcExt1();\n"
             "endclass\n"
             "interface class IntfExt2 extends IntfBase#(1);\n"
             "  pure virtual function bit funcExt2();\n"
             "endclass\n"
             "interface class IntfFinal extends IntfExt1, IntfExt2;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// The specialization discriminator admits any data type as the type argument,
// not just the built-in keyword types. Here the two branches parameterize the
// same base with distinct user typedefs (§6.18), so IntfBase#(NameA) and
// IntfBase#(NameB) are different interface class types and the parameter T
// inherited through both paths collides. Named-typedef operand counterpart of
// DifferentSpecializationsNotDiamondError (which uses keyword bit/logic args).
TEST(InterfaceClassDiamond, DifferentNamedTypeSpecializationsNotDiamondError) {
  ElabFixture f;
  ElabOk(
      "typedef bit NameA;\n"
      "typedef logic NameB;\n"
      "interface class IntfBase #(type T = int);\n"
      "  pure virtual function bit funcBase();\n"
      "endclass\n"
      "interface class IntfExt1 extends IntfBase#(NameA);\n"
      "  pure virtual function bit funcExt1();\n"
      "endclass\n"
      "interface class IntfExt2 extends IntfBase#(NameB);\n"
      "  pure virtual function bit funcExt2();\n"
      "endclass\n"
      "interface class IntfFinal extends IntfExt1, IntfExt2;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "is inherited from multiple interface classes and must be overridden", 12,
      "8.26.6.2"));
}

// §8.1 lets a class be declared wherever a data declaration may appear. Two
// different specializations of one interface class are not a diamond wherever
// they are written, and one specialization reached twice is; the pair below
// varies the scope alone.
TEST(InterfaceClassDiamond, DifferentSpecializationsInsideAModuleError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  interface class IBase #(type T = int);\n"
      "    pure virtual function void fb();\n"
      "  endclass\n"
      "  interface class IL extends IBase #(int);\n"
      "    pure virtual function void fl();\n"
      "  endclass\n"
      "  interface class IR extends IBase #(bit);\n"
      "    pure virtual function void fr();\n"
      "  endclass\n"
      "  interface class ID extends IL, IR;\n"
      "    pure virtual function void fd();\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "is inherited from multiple interface classes and must be overridden", 11,
      "8.26.6.2"));
}

TEST(InterfaceClassDiamond, SameSpecializationInsideAModuleOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  interface class IBase #(type T = int);\n"
             "    pure virtual function void fb();\n"
             "  endclass\n"
             "  interface class IL extends IBase #(int);\n"
             "    pure virtual function void fl();\n"
             "  endclass\n"
             "  interface class IR extends IBase #(int);\n"
             "    pure virtual function void fr();\n"
             "  endclass\n"
             "  interface class ID extends IL, IR;\n"
             "    pure virtual function void fd();\n"
             "  endclass\n"
             "endmodule\n"));
}

}  // namespace
