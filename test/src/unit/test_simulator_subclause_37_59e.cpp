#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

#include "fixture_vpi_run.h"
#include "helpers_sealed_design_run.h"
#include "preprocessor/protect_processing.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class ExpressionsEverywhere : public VpiDesignRun {
 protected:
  static vpiHandle FirstRhsIn(vpiHandle scope) {
    const std::vector<vpiHandle> kAssigns = ObjectsOf(vpiContAssign, scope);
    return kAssigns.empty() ? nullptr : vpi_handle(vpiRhs, kAssigns[0]);
  }

  static std::vector<vpiHandle> InitialRightSides() {
    std::vector<vpiHandle> sides;
    const std::vector<vpiHandle> kProcs = ObjectsOf(vpiProcess, By("top"));
    if (kProcs.empty()) return sides;
    vpiHandle body = vpi_handle(vpiStmt, kProcs[0]);
    if (vpi_get(vpiType, body) == vpiAssignment) {
      sides.push_back(vpi_handle(vpiRhs, body));
      return sides;
    }
    for (vpiHandle stmt : ObjectsOf(vpiStmt, body)) {
      sides.push_back(vpi_handle(vpiRhs, stmt));
    }
    return sides;
  }

  static vpiHandle InitialRhs(std::size_t n) {
    const std::vector<vpiHandle> kSides = InitialRightSides();
    return n < kSides.size() ? kSides[n] : nullptr;
  }

  static int IntOf(vpiHandle expr) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    value.value.integer = -1;
    vpi_get_value(expr, &value);
    return value.value.integer;
  }

  static std::string NameOf(vpiHandle obj) {
    const char* name = obj == nullptr ? nullptr : vpi_get_str(vpiName, obj);
    return name == nullptr ? "" : name;
  }

  static std::string DecompileOf(vpiHandle obj) {
    const char* text =
        obj == nullptr ? nullptr : vpi_get_str(vpiDecompile, obj);
    return text == nullptr ? "" : text;
  }

  static void ExpectMultiplierThen(vpiHandle op, int op_type,
                                   const std::vector<std::string>& names) {
    ASSERT_NE(op, nullptr);
    EXPECT_EQ(OpOf(op), op_type);
    const std::vector<vpiHandle> kOperands = OperandsOf(op);
    ASSERT_EQ(kOperands.size(), names.size() + 1);
    EXPECT_EQ(vpi_get(vpiType, kOperands[0]), vpiConstant);
    EXPECT_EQ(IntegerOf(kOperands[0]), 2);
    for (std::size_t n = 0; n < names.size(); ++n) {
      EXPECT_EQ(NameOf(kOperands[n + 1]), names[n]) << n;
    }
  }

  static void ExpectValues(vpiHandle pattern, const std::vector<int>& values) {
    ASSERT_NE(pattern, nullptr);
    EXPECT_EQ(OpOf(pattern), vpiAssignmentPatternOp);
    std::vector<int> found;
    for (vpiHandle operand : OperandsOf(pattern)) {
      found.push_back(IntOf(operand));
    }
    EXPECT_EQ(found, values);
  }
};

TEST(ExpressionClass, DISABLED_NetsAndVariablesAreExpressions) {
  for (int type : {vpiNet, vpiNetBit, vpiReg, vpiRegBit, vpiLogicVar,
                   vpiIntegerVar, vpiVarBit, vpiArrayVar, vpiStructVar}) {
    EXPECT_TRUE(VpiIsExprType(type)) << type;
  }
}

constexpr const char* kTableSelects =
    "module top; logic [0:3][7:0] r [1:4]; int j;\n"
    "  logic [0:3][7:0] s [0:2]; wire [1:0] w1; wire [31:0] w2;\n"
    "  assign w1 = r[4][3][1:0];\n"
    "  assign w2 = r[1][j-:4];\n"
    "  initial s = r[1:3];\n"
    "endmodule\n";

TEST_F(ExpressionsEverywhere, ASelectOfABitOfAnElementHasThatBitAsParent) {
  Run(kTableSelects);
  vpiHandle select = FirstRhsIn(By("top"));
  ASSERT_NE(select, nullptr);
  EXPECT_EQ(vpi_get(vpiType, select), vpiPartSelect);
  vpiHandle parent = vpi_handle(vpiParent, select);
  ASSERT_NE(parent, nullptr);
  EXPECT_EQ(vpi_get(vpiSize, parent), 8);
  vpiHandle element = vpi_handle(vpiParent, parent);
  ASSERT_NE(element, nullptr);
  EXPECT_EQ(VpiObjectOf(element),
            VpiObjectOf(vpi_handle_by_index(By("top.r"), 4)));
}

TEST_F(ExpressionsEverywhere, AnIndexedSelectOfAnElementHasTheElementAsParent) {
  Run(kTableSelects);
  const std::vector<vpiHandle> kAssigns = ObjectsOf(vpiContAssign, By("top"));
  ASSERT_EQ(kAssigns.size(), 2U);
  vpiHandle select = vpi_handle(vpiRhs, kAssigns[1]);
  ASSERT_NE(select, nullptr);
  EXPECT_EQ(vpi_get(vpiType, select), vpiIndexedPartSelect);
  vpiHandle parent = vpi_handle(vpiParent, select);
  ASSERT_NE(parent, nullptr);
  EXPECT_EQ(vpi_get(vpiSize, parent), 32);
  EXPECT_EQ(VpiObjectOf(parent),
            VpiObjectOf(vpi_handle_by_index(By("top.r"), 1)));
}

TEST_F(ExpressionsEverywhere, ASliceOfAnArrayHasTheArrayAsParent) {
  Run(kTableSelects);
  vpiHandle select = InitialRhs(0);
  ASSERT_NE(select, nullptr);
  EXPECT_EQ(vpi_get(vpiType, select), vpiPartSelect);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, select)),
            VpiObjectOf(By("top.r")));
}

constexpr std::string_view kExprKey = "expression-exchange-key";

TEST_F(ExpressionsEverywhere, DISABLED_AProtectedExpressionReportsItsSize) {
  RunUnderKey(
      EncryptEnvelopes("`pragma protect begin\n"
                       "module sealed(input [3:0] a, b, output [3:0] y);\n"
                       "  assign y = a & b;\n"
                       "endmodule\n"
                       "`pragma protect end\n"
                       "module t; wire [3:0] a, b, y;\n"
                       "  sealed s(a, b, y);\n"
                       "endmodule\n",
                       kExprKey),
      kExprKey, f_);
  ASSERT_FALSE(f_.has_errors);
  VpiObject* assign = nullptr;
  for (VpiObject* child : VpiObjectOf(By("t.s"))->children) {
    if (child->type == vpiContAssign) assign = child;
  }
  ASSERT_NE(assign, nullptr);
  ASSERT_NE(assign->rhs, nullptr);
  vpiHandle expr = VpiHandleOf(assign->rhs);
  EXPECT_EQ(vpi_get(vpiIsProtected, expr), 1);
  EXPECT_EQ(vpi_get(vpiSize, expr), 4);
  s_vpi_error_info info = {};
  const int kError = vpi_chk_error(&info);
  EXPECT_EQ(kError, 0);
}

TEST_F(ExpressionsEverywhere, DISABLED_BitAndVarSelectsReachATypespec) {
  Run("module top; logic [7:0] v; logic [7:0] arr [0:3]; int i;\n"
      "  logic b; logic [7:0] e;\n"
      "  initial begin b = v[i]; e = arr[i]; end\n"
      "endmodule\n");
  for (std::size_t n = 0; n < 2; ++n) {
    vpiHandle select = InitialRhs(n);
    ASSERT_NE(select, nullptr) << n;
    EXPECT_NE(vpi_handle(vpiTypespec, select), nullptr) << n;
  }
}

constexpr const char* kTypedPatterns =
    "module top; typedef logic [1:0] pair_t [0:1]; pair_t p, q; logic [1:0] "
    "a, b;\n"
    "  initial begin p = pair_t'{a, b}; q = pair_t'{2{a}}; end\n"
    "endmodule\n";

TEST_F(ExpressionsEverywhere, DISABLED_ATypedPatternReachesItsType) {
  Run(kTypedPatterns);
  vpiHandle pattern = InitialRhs(0);
  ASSERT_NE(pattern, nullptr);
  EXPECT_EQ(OpOf(pattern), vpiAssignmentPatternOp);
  EXPECT_EQ(NameOf(vpi_handle(vpiTypespec, pattern)), "pair_t");
}

TEST_F(ExpressionsEverywhere, DISABLED_ATypedReplicatedPatternReachesItsType) {
  Run(kTypedPatterns);
  vpiHandle pattern = InitialRhs(1);
  ASSERT_NE(pattern, nullptr);
  EXPECT_EQ(OpOf(pattern), vpiMultiAssignmentPatternOp);
  EXPECT_EQ(NameOf(vpi_handle(vpiTypespec, pattern)), "pair_t");
}

TEST_F(ExpressionsEverywhere, ADollarInAnAssertionRangeIsUnbounded) {
  Run("module top; logic a, b;\n"
      "  sequence s1; a ##[1:$] b; endsequence\n"
      "  sequence s2; ##[1:$] a; endsequence\n"
      "  sequence s3; a [*1:$]; endsequence\n"
      "  sequence s4; a [->1:$]; endsequence\n"
      "  sequence s5; a [=1:$]; endsequence\n"
      "endmodule\n");
  const struct {
    const char* name;
    int op;
  } kRanges[] = {{"s1", vpiCycleDelayOp},
                 {"s2", vpiUnaryCycleDelayOp},
                 {"s3", vpiConsecutiveRepeatOp},
                 {"s4", vpiGotoRepeatOp},
                 {"s5", vpiRepeatOp}};
  for (const auto& range : kRanges) {
    vpiHandle op =
        vpi_handle(vpiExpr, Named(vpiSequenceDecl, By("top"), range.name));
    ASSERT_NE(op, nullptr) << range.name;
    EXPECT_EQ(OpOf(op), range.op) << range.name;
    const std::vector<vpiHandle> kOperands = OperandsOf(op);
    ASSERT_FALSE(kOperands.empty()) << range.name;
    EXPECT_EQ(vpi_get(vpiConstType, kOperands.back()), vpiUnboundedConst)
        << range.name;
  }
}

TEST_F(ExpressionsEverywhere,
       DISABLED_EachLiteralReportsTheConstantTypeOfItsKind) {
  Run("module top; logic [11:0] x; real r; string s;\n"
      "  initial begin\n"
      "    x = 8'hFF; x = 12; x = 4'd9; x = 4'b1010; x = 6'o17;\n"
      "    r = 1.5; s = \"s\";\n"
      "  end\n"
      "endmodule\n");
  const std::vector<int> kTypes = {vpiHexConst,    vpiDecConst, vpiDecConst,
                                   vpiBinaryConst, vpiOctConst, vpiRealConst,
                                   vpiStringConst};
  const std::vector<vpiHandle> kSides = InitialRightSides();
  ASSERT_EQ(kSides.size(), kTypes.size());
  for (std::size_t n = 0; n < kSides.size(); ++n) {
    EXPECT_EQ(vpi_get(vpiType, kSides[n]), vpiConstant) << n;
    EXPECT_EQ(vpi_get(vpiConstType, kSides[n]), kTypes[n]) << n;
  }
}

TEST_F(ExpressionsEverywhere, AnOperationsValueIsWhatItEvaluatesToNow) {
  Run("module top; logic [3:0] a = 4'd3, b = 4'd4; wire [3:0] y;\n"
      "  assign y = a + b;\n"
      "endmodule\n");
  vpiHandle sum = FirstRhsIn(By("top"));
  ASSERT_NE(sum, nullptr);
  EXPECT_EQ(OpOf(sum), vpiAddOp);
  EXPECT_EQ(IntOf(sum), 7);
  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = 9;
  vpi_put_value(By("top.a"), &value, nullptr, vpiNoDelay);
  EXPECT_EQ(IntOf(sum), 13);
}

TEST_F(ExpressionsEverywhere, DISABLED_AnInsideSetsRangeIsARangeOperand) {
  Run("module top; logic [7:0] a; logic x;\n"
      "  initial x = a inside {1, [2:3]};\n"
      "endmodule\n");
  vpiHandle op = InitialRhs(0);
  ASSERT_NE(op, nullptr);
  EXPECT_EQ(OpOf(op), vpiInsideOp);
  const std::vector<vpiHandle> kOperands = OperandsOf(op);
  ASSERT_EQ(kOperands.size(), 3U);
  EXPECT_EQ(NameOf(kOperands[0]), "a");
  EXPECT_EQ(IntegerOf(kOperands[1]), 1);
  ASSERT_EQ(vpi_get(vpiType, kOperands[2]), vpiRange);
  EXPECT_EQ(IntegerOf(vpi_handle(vpiLeftRange, kOperands[2])), 2);
  EXPECT_EQ(IntegerOf(vpi_handle(vpiRightRange, kOperands[2])), 3);
}

TEST_F(ExpressionsEverywhere, AnInterfaceExpressionIsAnOperand) {
  Run("interface ifc; endinterface\n"
      "module top; ifc i0(); ifc i1();\n"
      "  virtual ifc v1 = i0, v2 = i1, v; logic s;\n"
      "  initial v = s ? v1 : v2;\n"
      "endmodule\n");
  vpiHandle op = InitialRhs(0);
  ASSERT_NE(op, nullptr);
  EXPECT_EQ(OpOf(op), vpiConditionOp);
  const std::vector<vpiHandle> kOperands = OperandsOf(op);
  ASSERT_EQ(kOperands.size(), 3U);
  for (std::size_t n = 1; n < 3; ++n) {
    EXPECT_EQ(vpi_get(vpiType, kOperands[n]), vpiVirtualInterfaceVar) << n;
  }
  EXPECT_EQ(NameOf(kOperands[1]), "v1");
  EXPECT_EQ(NameOf(kOperands[2]), "v2");
}

TEST_F(ExpressionsEverywhere, AMultipleConcatenationListsEveryElement) {
  Run("module top; logic [1:0] a, b; wire [7:0] y;\n"
      "  assign y = {2{a, b}};\n"
      "endmodule\n");
  ExpectMultiplierThen(FirstRhsIn(By("top")), vpiMultiConcatOp, {"a", "b"});
}

TEST_F(ExpressionsEverywhere, APartSelectsConstantSelectFollowsItsParent) {
  Run("module top; logic [7:0] r [0:3]; logic [7:0] d []; logic [7:0] q [$];\n"
      "  int i; logic [3:0] x;\n"
      "  initial begin\n"
      "    x = r[i][3:0]; x = r[1][3:0]; x = d[0][3:0]; x = q[0][3:0];\n"
      "    x = q[$][3:0];\n"
      "  end\n"
      "endmodule\n");
  const std::vector<int> kConstant = {0, 1, 0, 0, 0};
  const std::vector<vpiHandle> kSides = InitialRightSides();
  ASSERT_EQ(kSides.size(), kConstant.size());
  for (std::size_t n = 0; n < kSides.size(); ++n) {
    EXPECT_EQ(vpi_get(vpiType, kSides[n]), vpiPartSelect) << n;
    EXPECT_EQ(vpi_get(vpiConstantSelect, kSides[n]), kConstant[n]) << n;
  }
}

TEST_F(ExpressionsEverywhere, ACastHasOnlyTheCastExpressionAsOperand) {
  Run("module top; logic [7:0] a; int x;\n"
      "  initial x = int'(a);\n"
      "endmodule\n");
  vpiHandle cast = InitialRhs(0);
  ASSERT_NE(cast, nullptr);
  EXPECT_EQ(OpOf(cast), vpiCastOp);
  const std::vector<vpiHandle> kOperands = OperandsOf(cast);
  ASSERT_EQ(kOperands.size(), 1U);
  EXPECT_EQ(NameOf(kOperands[0]), "a");
  EXPECT_NE(vpi_handle(vpiTypespec, cast), nullptr);
}

constexpr const char* kNestedPatterns =
    "module top;\n"
    "  typedef struct { logic f; int g; } inner_t;\n"
    "  typedef struct { int n; inner_t p, q; } outer_t;\n"
    "  outer_t s, t;\n"
    "  initial begin\n"
    "    s = '{p: '{1'b1, 2}, int: 5, q: '{default: 0}};\n"
    "    t = '{n: 4, inner_t: '{f: 1'b1, g: 3}};\n"
    "  end\n"
    "endmodule\n";

TEST_F(ExpressionsEverywhere,
       DISABLED_MemberKeyedSubPatternsStayNestedInPlace) {
  Run(kNestedPatterns);
  vpiHandle pattern = InitialRhs(0);
  ASSERT_NE(pattern, nullptr);
  EXPECT_EQ(OpOf(pattern), vpiAssignmentPatternOp);
  const std::vector<vpiHandle> kOperands = OperandsOf(pattern);
  ASSERT_EQ(kOperands.size(), 3U);
  EXPECT_EQ(IntOf(kOperands[0]), 5);
  ExpectValues(kOperands[1], {1, 2});
  ExpectValues(kOperands[2], {0, 0});
}

TEST_F(ExpressionsEverywhere,
       DISABLED_ATypeKeyedSubPatternFillsEachMemberOfItsType) {
  Run(kNestedPatterns);
  vpiHandle pattern = InitialRhs(1);
  ASSERT_NE(pattern, nullptr);
  EXPECT_EQ(OpOf(pattern), vpiAssignmentPatternOp);
  const std::vector<vpiHandle> kOperands = OperandsOf(pattern);
  ASSERT_EQ(kOperands.size(), 3U);
  EXPECT_EQ(IntOf(kOperands[0]), 4);
  ExpectValues(kOperands[1], {1, 3});
  ExpectValues(kOperands[2], {1, 3});
}

constexpr const char* kReplicatedPatterns =
    "module top; bit x, y; bit u [0:3]; bit ub [1:0];\n"
    "  initial begin u = '{2 {x, y}}; ub = '{2 {y}}; ub = '{x, y}; end\n"
    "endmodule\n";

TEST_F(ExpressionsEverywhere, AReplicatedPatternListsEveryExpression) {
  Run(kReplicatedPatterns);
  ExpectMultiplierThen(InitialRhs(0), vpiMultiAssignmentPatternOp, {"x", "y"});
}

TEST_F(ExpressionsEverywhere, AProceduralReplicatedPatternIsTheOperation) {
  Run(kReplicatedPatterns);
  ExpectMultiplierThen(InitialRhs(1), vpiMultiAssignmentPatternOp, {"y"});
}

TEST_F(ExpressionsEverywhere, DISABLED_AssignmentPatternsDecompileAsWritten) {
  Run(kReplicatedPatterns);
  EXPECT_EQ(DecompileOf(InitialRhs(1)), "'{2{y}}");
  EXPECT_EQ(DecompileOf(InitialRhs(2)), "'{x, y}");
}

TEST_F(ExpressionsEverywhere, DISABLED_ATypedPatternDecompilesWithItsType) {
  Run(kTypedPatterns);
  EXPECT_EQ(DecompileOf(InitialRhs(0)), "pair_t'{a, b}");
}

}  // namespace
}  // namespace delta
