#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

std::string StaticMethodBodySrc(const std::string& stmt, bool declares_i) {
  return "class C;\n"
         "  int i;\n"
         "  static task t();\n"
         "    begin\n"
         "      int k;\n"
         "      logic [7:0] a;\n"
         "      int arr[4];\n" +
         std::string(declares_i ? "      int i;\n" : "") + "      " + stmt +
         "\n"
         "    end\n"
         "  endtask\n"
         "endclass\n"
         "module m;\n"
         "  C c;\n"
         "endmodule\n";
}

void ExpectPropertyAccessReported(const std::string& stmt) {
  ElabFixture f;
  std::string src = StaticMethodBodySrc(stmt, false);
  ElabOk(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "static method shall not access non-static members",
                            LineHolding(src, "static task"), "8.10"));
}

void ExpectBlockLocalAccepted(const std::string& stmt) {
  EXPECT_TRUE(ElabOk(StaticMethodBodySrc(stmt, true)));
}

TEST(StaticMethodExprPositions, PropertyInAForConditionIsReported) {
  ExpectPropertyAccessReported("for (int j = 0; j < i; j = j + 1) k = j;");
}

TEST(StaticMethodExprPositions, BlockLocalInAForConditionIsAccepted) {
  ExpectBlockLocalAccepted("for (int j = 0; j < i; j = j + 1) k = j;");
}

TEST(StaticMethodExprPositions, PropertyInAVariableInitializerIsReported) {
  ExpectPropertyAccessReported("int j = i;");
}

TEST(StaticMethodExprPositions, BlockLocalInAVariableInitializerIsAccepted) {
  ExpectBlockLocalAccepted("int j = i;");
}

TEST(StaticMethodExprPositions, PropertyInADelayControlIsReported) {
  ExpectPropertyAccessReported("#(i) k = 1;");
}

TEST(StaticMethodExprPositions, BlockLocalInADelayControlIsAccepted) {
  ExpectBlockLocalAccepted("#(i) k = 1;");
}

TEST(StaticMethodExprPositions, PropertyInACycleDelayIsReported) {
  ExpectPropertyAccessReported("##(i) k = 1;");
}

TEST(StaticMethodExprPositions, BlockLocalInACycleDelayIsAccepted) {
  ExpectBlockLocalAccepted("##(i) k = 1;");
}

TEST(StaticMethodExprPositions, PropertyInAnImmediateAssertionIsReported) {
  ExpectPropertyAccessReported("assert (i);");
}

TEST(StaticMethodExprPositions, BlockLocalInAnImmediateAssertionIsAccepted) {
  ExpectBlockLocalAccepted("assert (i);");
}

TEST(StaticMethodExprPositions, PropertyInARepeatEventCountIsReported) {
  ExpectPropertyAccessReported("k = repeat (i) @(a) 1;");
}

TEST(StaticMethodExprPositions, BlockLocalInARepeatEventCountIsAccepted) {
  ExpectBlockLocalAccepted("k = repeat (i) @(a) 1;");
}

TEST(StaticMethodExprPositions, PropertyInAnEventExpressionIsReported) {
  ExpectPropertyAccessReported("@(i) k = 1;");
}

TEST(StaticMethodExprPositions, BlockLocalInAnEventExpressionIsAccepted) {
  ExpectBlockLocalAccepted("@(i) k = 1;");
}

TEST(StaticMethodExprPositions, PropertyInAnEventIffConditionIsReported) {
  ExpectPropertyAccessReported("@(a iff i) k = 1;");
}

TEST(StaticMethodExprPositions, BlockLocalInAnEventIffConditionIsAccepted) {
  ExpectBlockLocalAccepted("@(a iff i) k = 1;");
}

TEST(StaticMethodExprPositions, PropertyInAWaitOrderListIsReported) {
  ElabFixture f;
  std::string src =
      "class C;\n"
      "  event i;\n"
      "  event j;\n"
      "  static task t();\n"
      "    wait_order (i, j);\n"
      "  endtask\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n";
  ElabOk(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "static method shall not access non-static members",
                            LineHolding(src, "static task"), "8.10"));
}

TEST(StaticMethodExprPositions, PropertyInARandcaseWeightIsReported) {
  ExpectPropertyAccessReported("randcase i : k = 1; endcase");
}

TEST(StaticMethodExprPositions, BlockLocalInARandcaseWeightIsAccepted) {
  ExpectBlockLocalAccepted("randcase i : k = 1; endcase");
}

TEST(StaticMethodExprPositions, PropertyInACaseItemPatternIsReported) {
  ExpectPropertyAccessReported("case (k) i: k = 1; endcase");
}

TEST(StaticMethodExprPositions, BlockLocalInACaseItemPatternIsAccepted) {
  ExpectBlockLocalAccepted("case (k) i: k = 1; endcase");
}

TEST(StaticMethodExprPositions, PropertyInAnUnpackedDimensionIsReported) {
  ExpectPropertyAccessReported("int arr2[i];");
}

TEST(StaticMethodExprPositions, BlockLocalInAnUnpackedDimensionIsAccepted) {
  ExpectBlockLocalAccepted("int arr2[i];");
}

TEST(StaticMethodExprPositions, PropertyInARandsequenceWeightIsReported) {
  ExpectPropertyAccessReported(
      "randsequence(main) main : alt := i; alt : { ; }; endsequence");
}

TEST(StaticMethodExprPositions, BlockLocalInARandsequenceWeightIsAccepted) {
  ExpectBlockLocalAccepted(
      "randsequence(main) main : alt := i; alt : { ; }; endsequence");
}

TEST(StaticMethodExprPositions, PropertyInAPartSelectUpperBoundIsReported) {
  ExpectPropertyAccessReported("k = a[3:i];");
}

TEST(StaticMethodExprPositions, BlockLocalInAPartSelectUpperBoundIsAccepted) {
  ExpectBlockLocalAccepted("k = a[3:i];");
}

TEST(StaticMethodExprPositions, PropertyInAReplicationCountIsReported) {
  ExpectPropertyAccessReported("k = {i{1'b0}};");
}

TEST(StaticMethodExprPositions, BlockLocalInAReplicationCountIsAccepted) {
  ExpectBlockLocalAccepted("k = {i{1'b0}};");
}

TEST(StaticMethodExprPositions, PropertyInAnAssignmentPatternKeyIsReported) {
  ExpectPropertyAccessReported("arr = '{i: 1};");
}

TEST(StaticMethodExprPositions, BlockLocalInAnAssignmentPatternKeyIsAccepted) {
  ExpectBlockLocalAccepted("arr = '{i: 1};");
}

std::string StaticMethodThisSrc(const std::string& stmt) {
  return "class C;\n"
         "  static int x;\n"
         "  static task t();\n"
         "    int k;\n"
         "    " +
         stmt +
         "\n"
         "  endtask\n"
         "endclass\n"
         "module m;\n"
         "  C c;\n"
         "endmodule\n";
}

void ExpectThisReported(const std::string& stmt) {
  ElabFixture f;
  std::string src = StaticMethodThisSrc(stmt);
  ElabOk(src, f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "'this' and 'super' shall not be used in a static method",
                    LineHolding(src, "static task"), "8.10"));
}

TEST(StaticMethodThisPositions, ThisInAForkArmIsReported) {
  ExpectThisReported(
      "fork\n"
      "      k = this.x;\n"
      "    join");
}

TEST(StaticMethodThisPositions, ThisInAForInitializationIsReported) {
  ExpectThisReported("for (k = this.x; k < 2; k = k + 1) ;");
}

TEST(StaticMethodThisPositions, ThisInAForStepIsReported) {
  ExpectThisReported("for (k = 0; k < 2; k = this.x) ;");
}

TEST(StaticMethodThisPositions, ThisInAnAssertionPassStmtIsReported) {
  ExpectThisReported("assert (1) k = this.x;");
}

TEST(StaticMethodThisPositions, ThisInAnAssertionFailStmtIsReported) {
  ExpectThisReported("assert (1) else k = this.x;");
}

TEST(StaticMethodThisPositions, ThisInARandcaseItemIsReported) {
  ExpectThisReported(
      "randcase\n"
      "      1 : k = this.x;\n"
      "    endcase");
}

TEST(StaticMethodThisPositions, ThisInARandsequenceCodeBlockIsReported) {
  ExpectThisReported(
      "randsequence(main)\n"
      "      main : { k = this.x; };\n"
      "    endsequence");
}

TEST(StaticMethodThisPositions, ThisInARandsequenceWeightCodeBlockIsReported) {
  ExpectThisReported(
      "randsequence(main)\n"
      "      main : alt := 5 { k = this.x; };\n"
      "      alt : { ; };\n"
      "    endsequence");
}

TEST(StaticMethodThisPositions, SuperInAForkArmIsReported) {
  ElabFixture f;
  std::string src =
      "class Base;\n"
      "  function void foo(); endfunction\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  static task t();\n"
      "    fork\n"
      "      super.foo();\n"
      "    join\n"
      "  endtask\n"
      "endclass\n"
      "module m;\n"
      "  Derived d;\n"
      "endmodule\n";
  ElabOk(src, f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "'this' and 'super' shall not be used in a static method",
                    LineHolding(src, "static task"), "8.10"));
}

std::string StaticMethodHandleSrc(const std::string& stmt) {
  return "class C;\n"
         "  int k = 9;\n"
         "  C kid;\n"
         "  static C m_inst;\n"
         "  function int get(); return k; endfunction\n"
         "  static function C make();\n"
         "    C h;\n"
         "    h = new;\n"
         "    return h;\n"
         "  endfunction\n"
         "  static function int f(C formal);\n"
         "    C c;\n"
         "    C arr[2];\n"
         "    " +
         stmt +
         "\n"
         "  endfunction\n"
         "endclass\n"
         "module m;\n"
         "  C c;\n"
         "endmodule\n";
}

void ExpectHandleAccessAccepted(const std::string& stmt) {
  EXPECT_TRUE(ElabOk(StaticMethodHandleSrc(stmt)));
}

void ExpectStaticFunctionFReported(const std::string& src) {
  ElabFixture f;
  ElabOk(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "static method shall not access non-static members",
                            LineHolding(src, "static function int f"), "8.10"));
}

void ExpectBareAccessReported(const std::string& stmt) {
  ExpectStaticFunctionFReported(StaticMethodHandleSrc(stmt));
}

TEST(StaticMethodHandleBases, PropertyThroughAStaticPropertyIsAccepted) {
  ExpectHandleAccessAccepted("return m_inst.k;");
}

TEST(StaticMethodHandleBases, PropertyThroughALocalHandleIsAccepted) {
  ExpectHandleAccessAccepted("return c.k;");
}

TEST(StaticMethodHandleBases, PropertyThroughAFormalIsAccepted) {
  ExpectHandleAccessAccepted("return formal.k;");
}

TEST(StaticMethodHandleBases, PropertyThroughACallResultIsAccepted) {
  ExpectHandleAccessAccepted("return make().k;");
}

TEST(StaticMethodHandleBases, PropertyThroughAnArrayElementIsAccepted) {
  ExpectHandleAccessAccepted("return arr[0].k;");
}

TEST(StaticMethodHandleBases, PropertyThroughAChainedHandleIsAccepted) {
  ExpectHandleAccessAccepted("return m_inst.kid.k;");
}

TEST(StaticMethodHandleBases, PropertyAssignedThroughALocalHandleIsAccepted) {
  ExpectHandleAccessAccepted("c.k = 1; return 0;");
}

TEST(StaticMethodHandleBases, MethodThroughAStaticPropertyIsAccepted) {
  ExpectHandleAccessAccepted("return m_inst.get();");
}

TEST(StaticMethodHandleBases, MethodThroughALocalHandleIsAccepted) {
  ExpectHandleAccessAccepted("return c.get();");
}

TEST(StaticMethodHandleBases, MethodThroughACallResultIsAccepted) {
  ExpectHandleAccessAccepted("return make().get();");
}

TEST(StaticMethodHandleBases, MethodThroughAnArrayElementIsAccepted) {
  ExpectHandleAccessAccepted("return arr[1].get();");
}

TEST(StaticMethodHandleBases, BarePropertyBesideTheHandlesIsReported) {
  ExpectBareAccessReported("return k;");
}

TEST(StaticMethodHandleBases, BareMethodCallBesideTheHandlesIsReported) {
  ExpectBareAccessReported("return get();");
}

TEST(StaticMethodHandleBases, PropertyBehindThisIsReported) {
  ExpectBareAccessReported("return this.k;");
}

TEST(StaticMethodHandleBases, PropertyThroughABareNonStaticHandleIsReported) {
  ExpectBareAccessReported("return kid.k;");
}

std::string ClassCWithStaticF(const std::string& stmt) {
  return "  class C;\n"
         "    int k = 9;\n"
         "    static C m_inst;\n"
         "    static function int f();\n"
         "      " +
         stmt +
         "\n"
         "    endfunction\n"
         "  endclass\n";
}

std::string PackageStaticMethodSrc(const std::string& stmt, bool imports) {
  return "package p;\n" + ClassCWithStaticF(stmt) +
         "endpackage\n"
         "module m;\n" +
         std::string(imports ? "  import p::*;\n  C c;\n" : "") + "endmodule\n";
}

void ExpectPackageBareAccessReported(bool imports) {
  ExpectStaticFunctionFReported(PackageStaticMethodSrc("return k;", imports));
}

TEST(StaticMethodInPackage, BarePropertyIsReportedWhereAModuleImportsIt) {
  ExpectPackageBareAccessReported(true);
}

TEST(StaticMethodInPackage, BarePropertyIsReportedWhereNoModuleImportsIt) {
  ExpectPackageBareAccessReported(false);
}

TEST(StaticMethodInPackage, PropertyThroughAStaticPropertyIsAccepted) {
  EXPECT_TRUE(ElabOk(PackageStaticMethodSrc("return m_inst.k;", true)));
}

std::string NestedClassSrc(const std::string& stmt) {
  return "class Outer;\n"
         "  class Inner;\n"
         "    int k = 9;\n"
         "    static Inner m_inst;\n"
         "    static function int f();\n"
         "      " +
         stmt +
         "\n"
         "    endfunction\n"
         "  endclass\n"
         "endclass\n";
}

std::string NestedUnitClassSrc(const std::string& stmt) {
  return NestedClassSrc(stmt) + "module m;\nendmodule\n";
}

std::string NestedModuleClassSrc(const std::string& stmt) {
  return "module m;\n" + NestedClassSrc(stmt) + "endmodule\n";
}

std::string NestedPackageClassSrc(const std::string& stmt) {
  return "package p;\n" + NestedClassSrc(stmt) +
         "endpackage\n"
         "module m;\n"
         "  import p::*;\n"
         "endmodule\n";
}

TEST(StaticMethodInNestedClass, BarePropertyIsReportedInAUnitClass) {
  ExpectStaticFunctionFReported(NestedUnitClassSrc("return k;"));
}

TEST(StaticMethodInNestedClass, BarePropertyIsReportedInAModuleClass) {
  ExpectStaticFunctionFReported(NestedModuleClassSrc("return k;"));
}

TEST(StaticMethodInNestedClass, BarePropertyIsReportedInAPackageClass) {
  ExpectStaticFunctionFReported(NestedPackageClassSrc("return k;"));
}

TEST(StaticMethodInNestedClass, PropertyThroughAStaticPropertyIsAccepted) {
  EXPECT_TRUE(ElabOk(NestedUnitClassSrc("return m_inst.k;")));
  EXPECT_TRUE(ElabOk(NestedPackageClassSrc("return m_inst.k;")));
}

std::string DesignElementStaticMethodSrc(const std::string& element,
                                         const std::string& stmt) {
  return element + " e;\n" + ClassCWithStaticF(stmt) + "end" + element +
         "\n"
         "module m;\n"
         "endmodule\n";
}

TEST(StaticMethodInDesignElement, BarePropertyIsReportedInAProgram) {
  ExpectStaticFunctionFReported(
      DesignElementStaticMethodSrc("program", "return k;"));
}

TEST(StaticMethodInDesignElement, BarePropertyIsReportedInAnInterface) {
  ExpectStaticFunctionFReported(
      DesignElementStaticMethodSrc("interface", "return k;"));
}

TEST(StaticMethodInDesignElement, PropertyThroughAStaticPropertyIsAccepted) {
  EXPECT_TRUE(
      ElabOk(DesignElementStaticMethodSrc("interface", "return m_inst.k;")));
}

}  // namespace
