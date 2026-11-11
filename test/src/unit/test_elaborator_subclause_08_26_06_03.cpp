#include <gtest/gtest.h>

#include <initializer_list>

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
      "8.26.6.3"));
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

TEST(InterfaceClassDiamond, DifferentSpecializationsMethodConflictError) {
  ElabFixture f;
  ElabOk(
      "module class_tb;\n"
      "  interface class ibase #(type T = logic);\n"
      "    pure virtual function void fn(T val);\n"
      "  endclass\n"
      "  interface class ic1 extends ibase#(bit);\n"
      "    pure virtual function void fn1();\n"
      "  endclass\n"
      "  interface class ic2 extends ibase#(string);\n"
      "    pure virtual function void fn2();\n"
      "  endclass\n"
      "  interface class ic3 extends ic1, ic2;\n"
      "    pure virtual function void fn3();\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "method name conflict for 'fn' in 'ic3'", 11,
                            "8.26.6.3"));
}

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
      "8.26.6.3"));
}

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
      "8.26.6.3"));
}

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
      "8.26.6.3"));
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

TEST(InterfaceClassSpecialization,
     TwoModuleLocalparamArgumentsAreTwoSpecializations) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  localparam int A = 1;\n"
      "  localparam int B = 2;\n"
      "  interface class IntfBase #(int P = 1);\n"
      "    parameter SIZE = 8;\n"
      "  endclass\n"
      "  interface class IntfExt1 extends IntfBase#(A);\n"
      "    pure virtual function bit funcExt1();\n"
      "  endclass\n"
      "  interface class IntfExt2 extends IntfBase#(B);\n"
      "    pure virtual function bit funcExt2();\n"
      "  endclass\n"
      "  interface class IntfFinal extends IntfExt1, IntfExt2;\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "is inherited from multiple interface classes and must be overridden", 13,
      "8.26.6.3"));
}

TEST(InterfaceClassSpecialization,
     AModuleLocalparamAndAnEqualLiteralAreOneSpecialization) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam int A = 2;\n"
      "  interface class IntfBase #(int P = 1);\n"
      "    parameter SIZE = 8;\n"
      "  endclass\n"
      "  interface class IntfExt1 extends IntfBase#(2);\n"
      "    pure virtual function bit funcExt1();\n"
      "  endclass\n"
      "  interface class IntfExt2 extends IntfBase#(A);\n"
      "    pure virtual function bit funcExt2();\n"
      "  endclass\n"
      "  interface class IntfFinal extends IntfExt1, IntfExt2;\n"
      "  endclass\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(InterfaceClassSpecialization,
     TwoLocalparamArgumentsAreTwoSpecializations) {
  ElabFixture f;
  ElabOk(
      "localparam int A = 1;\n"
      "localparam int B = 2;\n"
      "interface class IntfBase #(int P = 1);\n"
      "  parameter SIZE = 8;\n"
      "endclass\n"
      "interface class IntfExt1 extends IntfBase#(A);\n"
      "  pure virtual function bit funcExt1();\n"
      "endclass\n"
      "interface class IntfExt2 extends IntfBase#(B);\n"
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
      "8.26.6.3"));
}

TEST(InterfaceClassSpecialization,
     OneLocalparamArgumentReachedTwiceIsOneSpecialization) {
  EXPECT_TRUE(
      ElabOk("localparam int A = 1;\n"
             "interface class IntfBase #(int P = 1);\n"
             "  parameter SIZE = 8;\n"
             "endclass\n"
             "interface class IntfExt1 extends IntfBase#(A);\n"
             "  pure virtual function bit funcExt1();\n"
             "endclass\n"
             "interface class IntfExt2 extends IntfBase#(A);\n"
             "  pure virtual function bit funcExt2();\n"
             "endclass\n"
             "interface class IntfFinal extends IntfExt1, IntfExt2;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassSpecialization,
     ALiteralAndALocalparamOfEqualValueAreOneSpecialization) {
  EXPECT_TRUE(
      ElabOk("localparam int A = 2;\n"
             "interface class IntfBase #(int P = 1);\n"
             "  parameter SIZE = 8;\n"
             "endclass\n"
             "interface class IntfExt1 extends IntfBase#(2);\n"
             "  pure virtual function bit funcExt1();\n"
             "endclass\n"
             "interface class IntfExt2 extends IntfBase#(A);\n"
             "  pure virtual function bit funcExt2();\n"
             "endclass\n"
             "interface class IntfFinal extends IntfExt1, IntfExt2;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassDiamondElaboration,
     OneBaseMergesButTwoSpecializationsConflict) {
  ElabFixture f;
  ElaborateSrc(
      "interface class IntfBase; parameter SIZE = 64; endclass\n"
      "interface class IntfExt1 extends IntfBase; pure virtual function bit "
      "funcExt1(); endclass\n"
      "interface class IntfExt2 extends IntfBase; pure virtual function bit "
      "funcExt2(); endclass\n"
      "interface class IntfExt3 extends IntfExt1, IntfExt2; endclass\n"
      "class CD implements IntfExt1, IntfExt2;\n"
      "  virtual function bit funcExt1(); return 1; endfunction\n"
      "  virtual function bit funcExt2(); return 0; endfunction\n"
      "endclass\n"
      "interface class PB #(type T = int); pure virtual function bit "
      "funcBase(); endclass\n"
      "interface class PE1 extends PB#(bit); pure virtual function bit "
      "funcExt1(); endclass\n"
      "interface class PE2 extends PB#(logic); pure virtual function bit "
      "funcExt2(); endclass\n"
      "interface class PFinal extends PE1, PE2;\n"
      "  typedef bit T;\n"
      "  pure virtual function bit funcBase();\n"
      "endclass\n"
      "interface class PFinalNoT extends PE1, PE2;\n"
      "  pure virtual function bit funcBase();\n"
      "endclass\n"
      "interface class PSame1 extends PB#(bit); endclass\n"
      "interface class PSame2 extends PB#(bit); endclass\n"
      "interface class PSameF extends PSame1, PSame2; endclass\n"
      "module m;\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    r1 = IntfExt3::SIZE;\n"
      "    r2 = PSameF::T'(5);\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {16}) {
    EXPECT_TRUE(ReportedError(
        diags,
        "inherited from multiple interface classes and must be overridden",
        kLine, "8.26.6.3"))
        << kLine;
  }
  for (const int kLine : {4, 5, 12, 21}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

}  // namespace
