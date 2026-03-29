// §8.26.6.3

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

}  // namespace
