

#include "fixture_elaborator.h"

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

TEST(InterfaceClassDiamond, DifferentSpecializationsNotDiamondError) {
  EXPECT_FALSE(
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
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
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
  EXPECT_FALSE(
      ElabOk("interface class IntfBase #(int P = 1);\n"
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
             "endmodule\n"));
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
  EXPECT_FALSE(
      ElabOk("typedef bit NameA;\n"
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
             "endmodule\n"));
}

}  // namespace
