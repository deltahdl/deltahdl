#include <gtest/gtest.h>

#include <initializer_list>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(InheritanceElaboration, ClassExtendsOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  int x;\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  int y;\n"
             "endclass\n"
             "module m;\n"
             "  Derived d;\n"
             "endmodule\n"));
}

TEST(InheritanceElaboration, ExtendFinalClassError) {
  ElabFixture f;
  ElabOk(
      "class :final TopPacket;\n"
      "endclass\n"
      "class BrokenPacket extends TopPacket;\n"
      "endclass\n"
      "module m;\n"
      "  BrokenPacket b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot extend a class declared ':final'", 3,
                            "8.13"));
}

TEST(InheritanceElaboration, FinalClassAloneOk) {
  EXPECT_TRUE(
      ElabOk("class :final Sealed;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  Sealed s;\n"
             "endmodule\n"));
}

TEST(InheritanceElaboration, MultiLevelInheritanceOk) {
  EXPECT_TRUE(
      ElabOk("class A;\n"
             "endclass\n"
             "class B extends A;\n"
             "endclass\n"
             "class C extends B;\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(InheritanceElaboration, ExtendFinalInChainError) {
  ElabFixture f;
  ElabOk(
      "class A;\n"
      "endclass\n"
      "class :final B extends A;\n"
      "endclass\n"
      "class C extends B;\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot extend a class declared ':final'", 5,
                            "8.13"));
}

TEST(InheritanceElaboration, SubclassWithAdditionalMembersOk) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  int data;\n"
             "endclass\n"
             "class LinkedPacket extends Packet;\n"
             "  LinkedPacket next;\n"
             "  function LinkedPacket get_next();\n"
             "    get_next = next;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  LinkedPacket lp;\n"
             "endmodule\n"));
}

TEST(InheritanceElaboration, FinalDerivedClassOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  int x;\n"
             "endclass\n"
             "class :final Leaf extends Base;\n"
             "  int y;\n"
             "endclass\n"
             "module m;\n"
             "  Leaf l;\n"
             "endmodule\n"));
}

TEST(InheritanceElaboration, ClassExtendingItselfError) {
  ElabFixture f;
  ElabOk(
      "class A extends A;\n"
      "endclass\n"
      "module t;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class 'A' inherits from itself", 1, "8.13"));
}

TEST(InheritanceElaboration, MutualExtensionCycleReportedOnce) {
  ElabFixture f;
  ElabOk(
      "class A extends B;\n"
      "endclass\n"
      "class B extends A;\n"
      "endclass\n"
      "module t;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class 'A' inherits from itself", 1, "8.13"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "class 'B' inherits from itself", 3, "8.13"));
}

TEST(InheritanceElaboration, CycleReachedFromOutsideReportsItsOwnClass) {
  ElabFixture f;
  ElabOk(
      "class C extends A;\n"
      "endclass\n"
      "module t;\n"
      "  class A extends B;\n"
      "  endclass\n"
      "  class B extends A;\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class 'A' inherits from itself", 4, "8.13"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "class 'C' inherits from itself", 1, "8.13"));
}

TEST(InheritanceElaboration, NestedClassExtendingItselfError) {
  ElabFixture f;
  ElabOk(
      "class Outer;\n"
      "  class In extends In;\n"
      "  endclass\n"
      "endclass\n"
      "module t;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class 'In' inherits from itself", 2, "8.13"));
}

TEST(InheritanceElaboration, ExtendFinalClassFromAnyScopeIsAnError) {
  ElabFixture f;
  ElabOk(
      "class :final F; endclass\n"
      "package p;\n"
      "  class P extends F; endclass\n"
      "endpackage\n"
      "module m;\n"
      "  class :final G; endclass\n"
      "  class M extends G; endclass\n"
      "  class O;\n"
      "    class N extends F; endclass\n"
      "  endclass\n"
      "endmodule\n",
      f);
  for (const int kLine : {3, 7, 9}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "cannot extend a class declared ':final'", kLine,
                              "8.13"))
        << kLine;
  }
}

TEST(InheritanceElaboration, ABaseIsTheClassItsOwnScopeResolves) {
  ElabFixture f;
  ElabOk(
      "class :final J; endclass\n"
      "module a;\n"
      "  class :final K; endclass\n"
      "endmodule\n"
      "module b;\n"
      "  class K; endclass\n"
      "  class D extends K; endclass\n"
      "  class J; endclass\n"
      "  class DJ extends J; endclass\n"
      "endmodule\n"
      "module c;\n"
      "  class :final K; endclass\n"
      "  class E extends K; endclass\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  const char* const kMessage = "cannot extend a class declared ':final'";
  EXPECT_TRUE(ReportedError(diags, kMessage, 13, "8.13"));
  EXPECT_FALSE(ReportedError(diags, kMessage, 7, "8.13"));
  EXPECT_FALSE(ReportedError(diags, kMessage, 9, "8.13"));
}

TEST(InheritanceElaboration, ExtendFinalClassInEveryOtherPlaceIsAnError) {
  ElabFixture f;
  ElabOk(
      "class :final F; endclass\n"
      "class :final FP #(int N = 1); endclass\n"
      "class Open; endclass\n"
      "package pk;\n"
      "  class :final G; endclass\n"
      "endpackage\n"
      "class B1 extends Open; endclass\n"
      "class B2 extends pk::G; endclass\n"
      "class B3 extends FP #(3); endclass\n"
      "program pr;\n"
      "  class B4 extends F; endclass\n"
      "  class B5 extends Open; endclass\n"
      "endprogram\n"
      "interface itf;\n"
      "  class B6 extends F; endclass\n"
      "  class B7 extends Open; endclass\n"
      "endinterface\n"
      "module m;\n"
      "  if (1) begin : g\n"
      "    class B8 extends F; endclass\n"
      "    class B9 extends Open; endclass\n"
      "  end\n"
      "  F f;\n"
      "  FP #(2) fp;\n"
      "  initial begin f = new; fp = new; end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {8, 9, 11, 15, 20}) {
    EXPECT_TRUE(ReportedError(diags, "cannot extend a class declared ':final'",
                              kLine, "8.13"))
        << kLine;
  }
  for (const int kLine : {7, 12, 16, 21, 25}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

TEST(InheritanceElaboration,
     DISABLED_ExtendFinalClassThroughATypedefOrANestedSiblingIsAnError) {
  ElabFixture f;
  ElabOk(
      "class :final F; endclass\n"
      "typedef F FT;\n"
      "package pk;\n"
      "  class :final G; endclass\n"
      "  typedef G GT;\n"
      "endpackage\n"
      "class B1 extends FT; endclass\n"
      "class B2 extends pk::GT; endclass\n"
      "class Out;\n"
      "  class :final NF; endclass\n"
      "  class B3 extends NF; endclass\n"
      "endclass\n"
      "module m;\n"
      "  typedef F MT;\n"
      "  class B4 extends MT; endclass\n"
      "  class B5 extends Out; endclass\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {7, 8, 11, 15}) {
    EXPECT_TRUE(ReportedError(diags, "cannot extend a class declared ':final'",
                              kLine, "8.13"))
        << kLine;
  }
  EXPECT_FALSE(ErrorOnLine(diags, 16));
}

TEST(InheritanceElaboration,
     DISABLED_ALocalparamNamingAnInheritedParameterIsConstant) {
  ElabFixture f;
  ElabOk(
      "class D;\n"
      "  parameter int N = 5;\n"
      "  localparam int M = 7;\n"
      "  parameter logic [1:0][3:0] DQ = 8'h6c;\n"
      "  typedef struct packed { logic [3:0] a; logic [3:0] b; } st;\n"
      "  parameter st SP = '{4'h3, 4'h9};\n"
      "endclass\n"
      "class E extends D;\n"
      "  localparam V1 = N + 1;\n"
      "  localparam V2 = M;\n"
      "  localparam V3 = DQ[1];\n"
      "  localparam V4 = SP.b;\n"
      "endclass\n"
      "class F #(int P = 3) extends D;\n"
      "endclass\n"
      "class G extends F #(4);\n"
      "  localparam V5 = P * 2;\n"
      "endclass\n"
      "class H extends G;\n"
      "  localparam V6 = N + P + M;\n"
      "endclass\n"
      "interface class IA;\n"
      "  parameter int IN = 5;\n"
      "endclass\n"
      "interface class IB extends IA;\n"
      "  localparam V7 = IN + 1;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  for (const int kLine : {9, 10, 11, 12, 17, 20, 26}) {
    EXPECT_FALSE(ErrorOnLine(f.diag.Diagnostics(), kLine)) << kLine;
  }
}

}  // namespace
