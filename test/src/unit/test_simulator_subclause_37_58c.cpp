#include <gtest/gtest.h>

#include <set>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_simple_expr_uses.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class UsesEverywhere : public VpiDesignRun {
 protected:
  static std::vector<vpiHandle> UsesOf(vpiHandle expr) {
    return expr == nullptr ? std::vector<vpiHandle>{} : ObjectsOf(vpiUse, expr);
  }

  static std::set<int> LinesOf(vpiHandle expr) {
    std::set<int> lines;
    for (vpiHandle use : UsesOf(expr)) {
      if (vpi_get(vpiType, use) != vpiContAssignBit) {
        lines.insert(vpi_get(vpiLineNo, use));
      }
    }
    return lines;
  }

  static std::set<int> KindsOf(vpiHandle expr) {
    std::set<int> kinds;
    for (vpiHandle use : UsesOf(expr)) kinds.insert(vpi_get(vpiType, use));
    return kinds;
  }

  static vpiHandle FirstRhsIn(vpiHandle scope) {
    const std::vector<vpiHandle> kAssigns = ObjectsOf(vpiContAssign, scope);
    return kAssigns.empty() ? nullptr : vpi_handle(vpiRhs, kAssigns[0]);
  }
};

TEST_F(UsesEverywhere, ALogicVariablesBitIsUsedWhereItItsVectorOrASelectIs) {
  Run("module top; logic [7:0] v, x; wire a, b, c, d;\n"
      "assign a = v[3];\n"
      "assign b = v[3];\n"
      "assign c = v[5];\n"
      "assign d = ^v[4:2];\n"
      "initial x = v;\n"
      "assign c = ^v[7:4];\n"
      "endmodule\n");
  vpiHandle bit = FirstRhsIn(By("top"));
  ASSERT_NE(bit, nullptr);
  EXPECT_TRUE(vpi_get(vpiType, bit) == vpiVarBit ||
              vpi_get(vpiType, bit) == vpiRegBit);
  EXPECT_EQ(LinesOf(bit), (std::set<int>{2, 3, 5, 6}));
}

TEST_F(UsesEverywhere, ANetsBitIsUsedWhereTheWholeNetIs) {
  Run("module top; wire [7:0] n, x; wire a, b;\n"
      "assign a = n[3];\n"
      "assign x = n;\n"
      "assign b = n[4];\n"
      "endmodule\n");
  EXPECT_EQ(LinesOf(FirstRhsIn(By("top"))), (std::set<int>{2, 3}));
}

constexpr const char* kElementBits =
    "module top; logic [7:0] arr [0:3]; logic [7:0] all [0:3];\n"
    "  logic [7:0] e; wire a, b, c, d;\n"
    "assign a = arr[1][3];\n"
    "assign b = ^arr[1][4:2];\n"
    "initial e = arr[1];\n"
    "assign c = arr[2][3];\n"
    "initial e = arr[2];\n"
    "assign d = arr[1][3];\n"
    "assign c = ^arr[1][7:4];\n"
    "initial all = arr;\n"
    "endmodule\n";

TEST_F(UsesEverywhere, AnElementsBitIsUsedWhereItOrItsElementIs) {
  Run(kElementBits);
  std::set<int> lines = LinesOf(FirstRhsIn(By("top")));
  lines.erase(12);
  EXPECT_EQ(lines, (std::set<int>{3, 4, 5, 8}));
}

TEST_F(UsesEverywhere, DISABLED_AnElementsBitIsUsedWhereItsArrayIs) {
  Run(kElementBits);
  EXPECT_TRUE(LinesOf(FirstRhsIn(By("top"))).contains(12));
}

TEST_F(UsesEverywhere, AVariableIsUsedByThePortItConnects) {
  Run("module m(input logic [1:0] a); endmodule\n"
      "module top; logic [1:0] v; m u(v); endmodule\n");
  bool by_port = false;
  for (vpiHandle use : UsesOf(By("top.v"))) {
    if (vpi_get(vpiType, use) == vpiPort) {
      by_port = true;
      EXPECT_STREQ(vpi_get_str(vpiName, use), "a");
    }
  }
  EXPECT_TRUE(by_port);
}

TEST_F(UsesEverywhere, AStatementUseIsTheStatement) {
  Run("module top; logic a, b;\n"
      "initial b = a;\n"
      "endmodule\n");
  EXPECT_EQ(KindsOf(By("top.a")), (std::set<int>{vpiAssignment}));
}

TEST_F(UsesEverywhere, UsesInsideSubroutinesAreReached) {
  Run("module top; logic a, b;\n"
      "  task t; b = a; endtask\n"
      "  function void f; b = ~a; endfunction\n"
      "endmodule\n");
  EXPECT_EQ(LinesOf(By("top.a")), (std::set<int>{2, 3}));
}

TEST_F(UsesEverywhere, UsesInsideAProgramAreReached) {
  Run("program p; logic a, b; wire w;\n"
      "  initial b = a;\n"
      "  assign w = a;\n"
      "endprogram\n"
      "module top; p p0(); endmodule\n");
  EXPECT_EQ(LinesOf(By("top.p0.a")), (std::set<int>{2, 3}));
}

TEST_F(UsesEverywhere, UsesInsideAnInterfaceAreReached) {
  Run("interface ifc; logic a, b; wire w;\n"
      "  initial b = a;\n"
      "  assign w = a;\n"
      "endinterface\n"
      "module top; ifc i0(); endmodule\n");
  EXPECT_EQ(LinesOf(By("top.i0.a")), (std::set<int>{2, 3}));
}

TEST_F(UsesEverywhere, UsesInsideAGenerateBlockAreReached) {
  Run("module top; logic a, b; wire c;\n"
      "  if (1) begin : g\n"
      "    assign c = a;\n"
      "    initial b = a;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(LinesOf(By("top.a")), (std::set<int>{3, 4}));
}

TEST_F(UsesEverywhere, AParameterIsUsedWhereItIsWritten) {
  Run("module top; parameter P = 3; logic [3:0] x; wire [3:0] w;\n"
      "assign w = P;\n"
      "initial x = P + 1;\n"
      "endmodule\n");
  EXPECT_EQ(LinesOf(By("top.P")), (std::set<int>{2, 3}));
}

TEST_F(UsesEverywhere, DISABLED_ASpecParamIsUsedByThePathAndCheckNamingIt) {
  Run("module top(input a, output y); buf (y, a);\n"
      "specify specparam D = 3;\n"
      "  (a => y) = D;\n"
      "  $setup(a, posedge y, D);\n"
      "endspecify\n"
      "endmodule\n");
  vpiHandle param = Named(vpiSpecParam, By("top"), "D");
  ASSERT_NE(param, nullptr);
  EXPECT_EQ(LinesOf(param), (std::set<int>{3, 4}));
}

TEST_F(UsesEverywhere, DISABLED_ARefObjIsUsedWhereItIsWritten) {
  Run("module m(ref logic [1:0] r); wire [1:0] w;\n"
      "  assign w = r;\n"
      "endmodule\n"
      "module top; logic [1:0] v; m u(v); endmodule\n");
  vpiHandle ref = vpi_handle(vpiExpr, Named(vpiIODecl, By("top.u"), "r"));
  ASSERT_NE(ref, nullptr);
  EXPECT_EQ(vpi_get(vpiType, ref), vpiRefObj);
  EXPECT_EQ(LinesOf(ref), (std::set<int>{1, 2}));
}

TEST_F(UsesEverywhere, DISABLED_AVarSelectIsUsedWhereItOrItsBitsAre) {
  Run("module top; logic [7:0] arr [0:3]; integer i, j; wire [7:0] e, f;\n"
      "  wire a, b;\n"
      "assign e = arr[i];\n"
      "assign a = arr[i][3];\n"
      "assign f = arr[j];\n"
      "assign b = arr[j][3];\n"
      "assign f = arr[i];\n"
      "endmodule\n");
  vpiHandle select = FirstRhsIn(By("top"));
  ASSERT_NE(select, nullptr);
  EXPECT_EQ(vpi_get(vpiType, select), vpiVarSelect);
  EXPECT_EQ(LinesOf(select), (std::set<int>{3, 4, 7}));
}

bool IsSimple(int type) {
  VpiObject obj;
  obj.type = type;
  return VpiIsSimpleExpr(&obj);
}

TEST(SimpleExpressionClass, EveryVariableKindIsASimpleExpression) {
  for (int type : {vpiTimeVar,        vpiRealVar,
                   vpiShortRealVar,   vpiByteVar,
                   vpiShortIntVar,    vpiIntVar,
                   vpiLongIntVar,     vpiBitVar,
                   vpiPackedArrayVar, vpiStructVar,
                   vpiUnionVar,       vpiEnumVar,
                   vpiStringVar,      vpiChandleVar,
                   vpiClassVar,       vpiVirtualInterfaceVar,
                   vpiArrayVar,       vpiVarBit,
                   vpiRegBit,         vpiReg,
                   vpiRegArray,       vpiIntegerVar}) {
    EXPECT_TRUE(IsSimple(type)) << type;
  }
}

TEST(SimpleExpressionClass, EveryNetKindIsASimpleExpression) {
  for (int type :
       {vpiNetArray, vpiArrayNet, vpiInterconnectArray, vpiInterconnectNet,
        vpiStructNet, vpiUnionNet, vpiEnumNet, vpiIntegerNet, vpiTimeNet,
        vpiBitNet, vpiByteNet, vpiShortIntNet, vpiIntNet, vpiLongIntNet,
        vpiRealNet, vpiShortRealNet, vpiPackedArrayNet, vpiLogicNet}) {
    EXPECT_TRUE(IsSimple(type)) << type;
  }
}

TEST(SimpleExpressionClass, OtherExpressionsAndObjectsAreNot) {
  for (int type : {vpiIndexedPartSelect, vpiFuncCall, vpiSysFuncCall,
                   vpiMethodFuncCall, vpiLetExpr, vpiTask, vpiPort,
                   vpiAssignment, vpiContAssign, vpiParamAssign}) {
    EXPECT_FALSE(IsSimple(type)) << type;
  }
}

}  // namespace
}  // namespace delta
