#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

TEST(ExpressionModel, ExprClassGroupsItsMemberKinds) {
  for (int type : {vpiOperation, vpiConstant, vpiPartSelect,
                   vpiIndexedPartSelect, vpiFuncCall, vpiMethodFuncCall,
                   vpiSysFuncCall, vpiLetExpr, vpiRefObj}) {
    EXPECT_TRUE(VpiIsExprType(type)) << "type=" << type;
  }

  for (int type : {vpiParameter, vpiSpecParam, vpiVarSelect, vpiBitSelect}) {
    EXPECT_TRUE(VpiIsExprType(type)) << "simple expr type=" << type;
  }

  EXPECT_FALSE(VpiIsExprType(vpiReg));
  EXPECT_FALSE(VpiIsExprType(vpiNet));
  EXPECT_FALSE(VpiIsExprType(vpiModule));
}

TEST(ExpressionModel, MultiConcatOperandOrder) {
  VpiObject mult;
  VpiObject a;
  VpiObject b;

  auto operands = VpiMultiConcatOperands(&mult, {&a, &b});
  ASSERT_EQ(operands.size(), 3u);
  EXPECT_EQ(operands[0], &mult);
  EXPECT_EQ(operands[1], &a);
  EXPECT_EQ(operands[2], &b);

  auto just_mult = VpiMultiConcatOperands(&mult, {});
  ASSERT_EQ(just_mult.size(), 1u);
  EXPECT_EQ(just_mult[0], &mult);
}

TEST(ExpressionModel, MultiAssignmentPatternOperandOrder) {
  VpiObject mult;
  VpiObject y;

  auto operands = VpiMultiAssignmentPatternOperands(&mult, {&y});
  ASSERT_EQ(operands.size(), 2u);
  EXPECT_EQ(operands[0], &mult);
  EXPECT_EQ(operands[1], &y);
}

TEST(ExpressionModel, MultiAssignmentPatternMultiplierAloneWhenPatternEmpty) {
  VpiObject mult;

  auto operands = VpiMultiAssignmentPatternOperands(&mult, {});
  ASSERT_EQ(operands.size(), 1u);
  EXPECT_EQ(operands[0], &mult);
}

TEST(ExpressionModel, CastOpIsUnary) {
  VpiObject cast_arg;

  auto operands = VpiCastOpOperands(&cast_arg);
  ASSERT_EQ(operands.size(), 1u);
  EXPECT_EQ(operands[0], &cast_arg);
}

TEST(ExpressionModel, AssignmentPatternResolvesToPositional) {
  VpiObject member0;
  VpiObject member1;
  VpiObject def;

  std::vector<VpiAssignmentPatternEntry> positioned = {{0, &member0},
                                                       {2, &member1}};
  auto operands = VpiAssignmentPatternPositionalOperands(4, positioned, &def);
  ASSERT_EQ(operands.size(), 4u);
  EXPECT_EQ(operands[0], &member0);
  EXPECT_EQ(operands[1], &def);
  EXPECT_EQ(operands[2], &member1);
  EXPECT_EQ(operands[3], &def);
}

TEST(ExpressionModel, AssignmentPatternPreservesNesting) {
  VpiObject nested;
  nested.type = vpiOperation;
  nested.op_type = vpiAssignmentPatternOp;
  VpiObject def;

  auto operands =
      VpiAssignmentPatternPositionalOperands(2, {{0, &nested}}, &def);
  ASSERT_EQ(operands.size(), 2u);
  EXPECT_EQ(operands[0], &nested);
  EXPECT_EQ(operands[0]->op_type, vpiAssignmentPatternOp);
  EXPECT_EQ(operands[1], &def);
}

TEST(ExpressionModel, AssignmentPatternIgnoresOutOfRangePositions) {
  VpiObject good;
  VpiObject stray_high;
  VpiObject stray_neg;
  VpiObject def;

  std::vector<VpiAssignmentPatternEntry> entries = {
      {0, &good}, {5, &stray_high}, {-1, &stray_neg}};
  auto operands = VpiAssignmentPatternPositionalOperands(2, entries, &def);
  ASSERT_EQ(operands.size(), 2u);
  EXPECT_EQ(operands[0], &good);
  EXPECT_EQ(operands[1], &def);

  auto none = VpiAssignmentPatternPositionalOperands(0, {{0, &good}}, &def);
  EXPECT_TRUE(none.empty());
}

TEST(ExpressionModel, TypespecAvailabilityGuarantee) {
  EXPECT_TRUE(VpiTypespecAlwaysAvailable(0, true, false));

  EXPECT_TRUE(VpiTypespecAlwaysAvailable(vpiCastOp, false, false));

  EXPECT_TRUE(VpiTypespecAlwaysAvailable(vpiAssignmentPatternOp, false, true));
  EXPECT_TRUE(
      VpiTypespecAlwaysAvailable(vpiMultiAssignmentPatternOp, false, true));
  EXPECT_FALSE(
      VpiTypespecAlwaysAvailable(vpiAssignmentPatternOp, false, false));

  EXPECT_FALSE(VpiTypespecAlwaysAvailable(vpiAddOp, false, false));
}

TEST(ExpressionModel,
     MultiAssignmentPatternTypespecNotGuaranteedWithoutPrefix) {
  EXPECT_FALSE(
      VpiTypespecAlwaysAvailable(vpiMultiAssignmentPatternOp, false, false));
}

TEST(ExpressionModel, PartSelectConstantSelectRequiresAllThreeConditions) {
  VpiPartSelectConstantSelectQuery all_true;
  all_true.parent_constant_select = true;
  all_true.parent_array_has_static_bounds = true;
  all_true.all_range_exprs_constant = true;
  EXPECT_TRUE(VpiPartSelectConstantSelect(all_true));

  VpiPartSelectConstantSelectQuery q1 = all_true;
  q1.parent_constant_select = false;
  EXPECT_FALSE(VpiPartSelectConstantSelect(q1));

  VpiPartSelectConstantSelectQuery q2 = all_true;
  q2.parent_array_has_static_bounds = false;
  EXPECT_FALSE(VpiPartSelectConstantSelect(q2));

  VpiPartSelectConstantSelectQuery q3 = all_true;
  q3.all_range_exprs_constant = false;
  EXPECT_FALSE(VpiPartSelectConstantSelect(q3));
}

TEST(ExpressionModel, PartSelectParentRemovesTrailingSelect) {
  EXPECT_EQ(VpiPartSelectParentExpr("r[4][3][1:0]"), "r[4][3]");
  EXPECT_EQ(VpiPartSelectParentExpr("r[i+1][3][j+:2]"), "r[i+1][3]");
  EXPECT_EQ(VpiPartSelectParentExpr("r[0][j-:4]"), "r[0]");
  EXPECT_EQ(VpiPartSelectParentExpr("r[0:2]"), "r");
}

TEST(ExpressionModel, PartSelectParentEdgeCases) {
  EXPECT_EQ(VpiPartSelectParentExpr("r"), "r");
  EXPECT_EQ(VpiPartSelectParentExpr("r[0:2]  "), "r");
}

TEST(ExpressionModel, DecompileJoinUsesSingleSpaces) {
  EXPECT_EQ(VpiDecompileJoin({"a", "+", "b"}), "a + b");

  EXPECT_EQ(VpiDecompileJoin({"a", "", "+", "", "b"}), "a + b");
  EXPECT_EQ(VpiDecompileJoin({"x"}), "x");
}

TEST(ExpressionModel, DecompileParenthesizeAddsNoWhitespace) {
  EXPECT_EQ(VpiDecompileParenthesize("a + b"), "(a + b)");

  std::string inner =
      VpiDecompileParenthesize(VpiDecompileJoin({"a", "+", "b"}));
  EXPECT_EQ(VpiDecompileJoin({inner, "*", "c"}), "(a + b) * c");
}

TEST(ExpressionModel, ConstantReportsConstType) {
  VpiContext ctx;
  VpiObject c;
  c.type = vpiConstant;
  c.const_type = vpiUnboundedConst;
  EXPECT_EQ(ctx.Get(vpiConstType, &c), vpiUnboundedConst);

  VpiObject unset;
  unset.type = vpiConstant;
  EXPECT_EQ(ctx.Get(vpiConstType, &unset), 0);
}

TEST(ExpressionModel, IndexedPartSelectReportsItsType) {
  VpiContext ctx;
  VpiObject ips;
  ips.type = vpiIndexedPartSelect;
  ips.indexed_part_select_type = vpiPosIndexed;
  EXPECT_EQ(ctx.Get(vpiIndexedPartSelectType, &ips), vpiPosIndexed);
}

TEST(ExpressionModel, IndexedPartSelectReportsNegativeAndUnsetType) {
  VpiContext ctx;

  VpiObject down;
  down.type = vpiIndexedPartSelect;
  down.indexed_part_select_type = vpiNegIndexed;
  EXPECT_EQ(ctx.Get(vpiIndexedPartSelectType, &down), vpiNegIndexed);

  VpiObject unset;
  unset.type = vpiIndexedPartSelect;
  EXPECT_EQ(ctx.Get(vpiIndexedPartSelectType, &unset), 0);
}

TEST(ExpressionModel, ProtectedExpressionPermitsVpiSize) {
  VpiContext ctx;
  VpiObject op;
  op.type = vpiOperation;
  op.size = 8;
  op.is_protected = true;

  EXPECT_EQ(ctx.Get(vpiSize, &op), 8);
  EXPECT_EQ(ctx.LastError().level, 0);
}

TEST(ExpressionModel, ProtectedExpressionStillGuardsOtherProperties) {
  VpiContext ctx;
  VpiObject op;
  op.type = vpiOperation;
  op.op_type = vpiAddOp;
  op.is_protected = true;

  EXPECT_EQ(ctx.Get(vpiOpType, &op), vpiUndefined);
  EXPECT_NE(ctx.LastError().level, 0);
}

TEST(ExpressionModel, ProtectedSimpleExpressionsPermitVpiSize) {
  VpiContext ctx;
  for (int type : {vpiReg, vpiNet, vpiIntVar}) {
    VpiObject simple;
    simple.type = type;
    simple.size = 16;
    simple.is_protected = true;
    EXPECT_EQ(ctx.Get(vpiSize, &simple), 16) << type;
    EXPECT_EQ(ctx.LastError().level, 0) << type;
  }
  VpiObject module;
  module.type = vpiModule;
  module.size = 16;
  module.is_protected = true;
  EXPECT_EQ(ctx.Get(vpiSize, &module), vpiUndefined);
  EXPECT_NE(ctx.LastError().level, 0);
}

class ExpressionsOfARun : public VpiDesignRun {
 protected:
  static vpiHandle Rhs() {
    vpiHandle it =
        vpi_iterate(vpiContAssign, vpi_handle_by_name(VpiText("top"), nullptr));
    if (it == nullptr) return nullptr;
    return vpi_handle(vpiRhs, vpi_scan(it));
  }

  static int IntOf(vpiHandle expr) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(expr, &value);
    return value.value.integer;
  }

  static std::vector<vpiHandle> OperandsOf(vpiHandle op) {
    std::vector<vpiHandle> operands;
    vpiHandle it = vpi_iterate(vpiOperand, op);
    if (it == nullptr) return operands;
    while (vpiHandle operand = vpi_scan(it)) operands.push_back(operand);
    return operands;
  }
};

constexpr const char* kPartSelect =
    "module top; wire [7:0] a; wire [3:0] y; assign y = a[7:4]; endmodule\n";

TEST_F(ExpressionsOfARun, APartSelectIsAPartSelectObject) {
  Run(kPartSelect);
  EXPECT_EQ(vpi_get(vpiType, Rhs()), vpiPartSelect);
}

TEST_F(ExpressionsOfARun, APartSelectsParentIsWhatItSelectsInto) {
  Run(kPartSelect);
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiParent, Rhs())), "a");
}

TEST_F(ExpressionsOfARun, APartSelectsLeftRangeIsItsFirstBound) {
  Run(kPartSelect);
  EXPECT_EQ(IntOf(vpi_handle(vpiLeftRange, Rhs())), 7);
}

TEST_F(ExpressionsOfARun, APartSelectsRightRangeIsItsSecondBound) {
  Run(kPartSelect);
  EXPECT_EQ(IntOf(vpi_handle(vpiRightRange, Rhs())), 4);
}

constexpr const char* kIndexedPartSelect =
    "module top; wire [7:0] a; wire [3:0] y; assign y = a[2 +: 4]; "
    "endmodule\n";

TEST_F(ExpressionsOfARun, AnIndexedPartSelectIsAnIndexedPartSelectObject) {
  Run(kIndexedPartSelect);
  EXPECT_EQ(vpi_get(vpiType, Rhs()), vpiIndexedPartSelect);
}

TEST_F(ExpressionsOfARun, AnAscendingIndexedPartSelectIsPosIndexed) {
  Run(kIndexedPartSelect);
  EXPECT_EQ(vpi_get(vpiIndexedPartSelectType, Rhs()), vpiPosIndexed);
}

TEST_F(ExpressionsOfARun, ADescendingIndexedPartSelectIsNegIndexed) {
  Run("module top; wire [7:0] a; wire [3:0] y; assign y = a[5 -: 4]; "
      "endmodule\n");
  EXPECT_EQ(vpi_get(vpiIndexedPartSelectType, Rhs()), vpiNegIndexed);
}

TEST_F(ExpressionsOfARun, AnIndexedPartSelectsBaseIsItsStart) {
  Run(kIndexedPartSelect);
  EXPECT_EQ(IntOf(vpi_handle(vpiBaseExpr, Rhs())), 2);
}

TEST_F(ExpressionsOfARun, AnIndexedPartSelectsWidthIsItsWidth) {
  Run(kIndexedPartSelect);
  EXPECT_EQ(IntOf(vpi_handle(vpiWidthExpr, Rhs())), 4);
}

TEST_F(ExpressionsOfARun, AnIndexedPartSelectsParentIsWhatItSelectsInto) {
  Run(kIndexedPartSelect);
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiParent, Rhs())), "a");
}

constexpr const char* kReplication =
    "module top; wire a; wire [1:0] y; assign y = {2{a}}; endmodule\n";

TEST_F(ExpressionsOfARun, AReplicationIsAMultiConcatOperation) {
  Run(kReplication);
  EXPECT_EQ(vpi_get(vpiOpType, Rhs()), vpiMultiConcatOp);
}

TEST_F(ExpressionsOfARun, AReplicationsFirstOperandIsTheMultiplier) {
  Run(kReplication);
  std::vector<vpiHandle> operands = OperandsOf(Rhs());
  ASSERT_EQ(operands.size(), 2U);
  EXPECT_EQ(IntOf(operands[0]), 2);
}

TEST_F(ExpressionsOfARun, AReplicationsLaterOperandsAreTheElements) {
  Run(kReplication);
  std::vector<vpiHandle> operands = OperandsOf(Rhs());
  ASSERT_EQ(operands.size(), 2U);
  EXPECT_STREQ(vpi_get_str(vpiName, operands[1]), "a");
}

TEST_F(ExpressionsOfARun, ACastIsACastOperation) {
  Run("module top; wire [7:0] a; wire [31:0] y; assign y = int'(a); "
      "endmodule\n");
  EXPECT_EQ(vpi_get(vpiOpType, Rhs()), vpiCastOp);
}

TEST_F(ExpressionsOfARun, AnInsideExpressionIsAnInsideOperation) {
  Run("module top; wire [7:0] a; wire y; assign y = a inside {1, 2}; "
      "endmodule\n");
  EXPECT_EQ(vpi_get(vpiOpType, Rhs()), vpiInsideOp);
}

TEST_F(ExpressionsOfARun, ARightToLeftStreamIsAStreamRLOperation) {
  Run("module top; wire [7:0] a, y; assign y = {<<{a}}; endmodule\n");
  EXPECT_EQ(vpi_get(vpiOpType, Rhs()), vpiStreamRLOp);
}

TEST_F(ExpressionsOfARun, ALeftToRightStreamIsAStreamLROperation) {
  Run("module top; wire [7:0] a, y; assign y = {>>{a}}; endmodule\n");
  EXPECT_EQ(vpi_get(vpiOpType, Rhs()), vpiStreamLROp);
}

TEST_F(ExpressionsOfARun, AMinTypMaxIsAMinTypMaxOperation) {
  Run("module top; wire a, b, c, y; assign y = (a:b:c); endmodule\n");
  EXPECT_EQ(vpi_get(vpiOpType, Rhs()), vpiMinTypMaxOp);
}

TEST_F(ExpressionsOfARun, AnImplicationIsAnImplyOperation) {
  Run("module top; wire a, b, y; assign y = (a -> b); endmodule\n");
  EXPECT_EQ(vpi_get(vpiOpType, Rhs()), vpiImplyOp);
}

TEST_F(ExpressionsOfARun, AnOperationDecompilesOneSpaceApart) {
  Run("module top; wire [7:0] a, b, y; assign y = a+b; endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, Rhs()), "a + b");
}

TEST_F(ExpressionsOfARun, ParenthesesStandWherePrecedenceNeedsThem) {
  Run("module top; wire [7:0] a, b, c, y; assign y = (a + b) * c; "
      "endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, Rhs()), "(a + b) * c");
}

TEST_F(ExpressionsOfARun, ParenthesesPrecedenceDoesNotNeedAreDropped) {
  Run("module top; wire [7:0] a, b, c, y; assign y = a + (b * c); "
      "endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, Rhs()), "a + b * c");
}

TEST_F(ExpressionsOfARun, ARightOperandOfALeftAssociativeOperatorStaysWhole) {
  Run("module top; wire [7:0] a, b, c, y; assign y = a - (b - c); "
      "endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, Rhs()), "a - (b - c)");
}

TEST_F(ExpressionsOfARun, AUnaryOperatorStandsOneSpaceFromItsOperand) {
  Run("module top; wire [7:0] a, b, y; assign y = ~(a & b) + -a; "
      "endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, Rhs()), "~ (a & b) + - a");
}

TEST_F(ExpressionsOfARun, AConditionalDecompilesWithItsOperators) {
  Run("module top; wire s, t; wire [7:0] a, b, y;\n"
      "  assign y = (s?t:s) ? a+1 : b; endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, Rhs()), "(s ? t : s) ? a + 1 : b");
}

TEST_F(ExpressionsOfARun, AConstantDecompilesToItsLiteral) {
  Run("module top; wire [7:0] y; assign y = 8'hA5; endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, Rhs()), "8'hA5");
}

TEST_F(ExpressionsOfARun, ASelectDecompilesAfterItsBase) {
  Run(kPartSelect);
  EXPECT_STREQ(vpi_get_str(vpiDecompile, Rhs()), "a[7:4]");
}

TEST_F(ExpressionsOfARun, AnIndexedPartSelectDecompilesAfterItsBase) {
  Run(kIndexedPartSelect);
  EXPECT_STREQ(vpi_get_str(vpiDecompile, Rhs()), "a[2+:4]");
}

TEST_F(ExpressionsOfARun, AConcatenationDecompilesWithItsElements) {
  Run("module top; wire [3:0] a, b; wire [7:0] y; assign y = {a,b}; "
      "endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, Rhs()), "{a, b}");
}

TEST_F(ExpressionsOfARun, AReplicationDecompilesWithItsMultiplier) {
  Run(kReplication);
  EXPECT_STREQ(vpi_get_str(vpiDecompile, Rhs()), "{2{a}}");
}

TEST_F(ExpressionsOfARun, ACallDecompilesWithItsArguments) {
  Run("module top;\n"
      "  function automatic int f(int x, int z); return x; endfunction\n"
      "  wire [31:0] a, y; assign y = f(a+1,a); endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, Rhs()), "f(a + 1, a)");
}

TEST_F(ExpressionsOfARun, AWithClauseDecompilesAfterItsCall) {
  Run("module top; int arr[3]; wire [31:0] y;\n"
      "  assign y = arr.sum() with (item*2); endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, Rhs()), "arr.sum() with (item * 2)");
}

TEST_F(ExpressionsOfARun, AnInlineConstraintBlockDecompilesAfterItsCall) {
  Run("module top; int a; wire [31:0] y;\n"
      "  assign y = std::randomize(a) with {a>0; soft a<9;}; endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, Rhs()),
               "std::randomize(a) with {a > 0; soft a < 9;}");
}

TEST_F(ExpressionsOfARun, ARestrictedBlockDecompilesWithItsIdentifierList) {
  Run("module top; class C; rand int x; endclass C c = new;\n"
      "  wire [31:0] y; assign y = c.randomize() with (x) {x>0;};\n"
      "endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, Rhs()),
               "c.randomize() with (x) {x > 0;}");
}

TEST_F(ExpressionsOfARun, AGoverningItemDecompilesWithItsSets) {
  Run("module top; int a, b; wire [31:0] y;\n"
      "  assign y = std::randomize(a, b) with {solve b before a;\n"
      "    b -> a!=0; if (b>1) a<4; else a>8;}; endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, Rhs()),
               "std::randomize(a, b) with {solve b before a; b -> {a != 0;} "
               "if (b > 1) {a < 4;} else {a > 8;}}");
}

TEST_F(ExpressionsOfARun, AConstraintItemDecompilesAsWritten) {
  Run("module top; int a, b; int q[4]; wire [31:0] y;\n"
      "  assign y = std::randomize(a, b) with {a dist {0:=1, [1:3]:/2};\n"
      "    unique {a, b}; foreach (q[i]) q[i]<a; disable soft a;};\n"
      "endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, Rhs()),
               "std::randomize(a, b) with {a dist {0 := 1, [1:3] :/ 2}; "
               "unique {a, b}; foreach (q[i]) {q[i] < a;} disable soft a;}");
}

TEST_F(ExpressionsOfARun, ACastDecompilesWithItsType) {
  Run("module top; wire [7:0] a; wire [31:0] y; assign y = int'(a+1); "
      "endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, Rhs()), "int'(a + 1)");
}

TEST_F(ExpressionsOfARun, AnInsideExpressionDecompilesWithItsSet) {
  Run("module top; wire [7:0] a; wire y; assign y = a inside {1,[2:3]}; "
      "endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, Rhs()), "a inside {1, [2:3]}");
}

TEST_F(ExpressionsOfARun, AStreamDecompilesWithItsDirection) {
  Run("module top; wire [7:0] a, y; assign y = {<<{a}}; endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, Rhs()), "{<< {a}}");
}

TEST_F(ExpressionsOfARun, AMinTypMaxDecompilesInItsParentheses) {
  Run("module top; wire a, b, c, y; assign y = (a:b:c); endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, Rhs()), "(a : b : c)");
}

TEST_F(ExpressionsOfARun, AnOperandDecompilesOnItsOwn) {
  Run("module top; wire [7:0] a, b, c, y; assign y = (a + b) * c; "
      "endmodule\n");
  std::vector<vpiHandle> operands = OperandsOf(Rhs());
  ASSERT_EQ(operands.size(), 2U);
  EXPECT_STREQ(vpi_get_str(vpiDecompile, operands[0]), "a + b");
}

std::vector<int>& ProbedArgumentKinds() {
  static std::vector<int> kinds;
  return kinds;
}

class ArgumentsOfARun : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    ProbedArgumentKinds().clear();
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText("$probe");
    data.calltf = [](PLI_BYTE8*) -> PLI_INT32 {
      vpiHandle it =
          vpi_iterate(vpiArgument, vpi_handle(vpiSysTfCall, nullptr));
      for (vpiHandle h = it != nullptr ? vpi_scan(it) : nullptr; h != nullptr;
           h = vpi_scan(it)) {
        ProbedArgumentKinds().push_back(vpi_get(vpiType, h));
      }
      return 0;
    };
    ASSERT_NE(vpi_register_systf(&data), nullptr);
  }
};

TEST_F(ArgumentsOfARun, ARunTimeArgumentIsTheKindOfExprItsActualIs) {
  Run("module top; int x;\n"
      "  function int inc(); return 1; endfunction\n"
      "  initial $probe(inc(), 5, x + 1, $time);\n"
      "endmodule\n");
  EXPECT_EQ(ProbedArgumentKinds(),
            (std::vector<int>{vpiFuncCall, vpiConstant, vpiOperation,
                              vpiSysFuncCall}));
}

TEST(ExpressionModel, OperandsAreTheOperationsExpressionChildren) {
  EXPECT_TRUE(VpiOperationOperands(nullptr).empty());
  VpiObject constant;
  constant.type = vpiConstant;
  EXPECT_TRUE(VpiOperationOperands(&constant).empty());
  VpiObject inst;
  inst.type = vpiPropertyInst;
  VpiObject attribute;
  attribute.type = vpiAttribute;
  VpiObject operation;
  operation.type = vpiOperation;
  operation.children = {&inst, &attribute};
  EXPECT_EQ(VpiOperationOperands(&operation), (std::vector<VpiHandle>{&inst}));
}

constexpr const char* kPairPrefix =
    "module top; typedef struct packed { logic a, b; } pair_t;\n"
    "  typedef struct packed { logic [1:0] a; } one_t;\n"
    "  logic x, y; logic [1:0] z; pair_t w; one_t v;\n";

void ExpectPatternOverXThenY(vpiHandle pattern) {
  ASSERT_NE(pattern, nullptr);
  EXPECT_EQ(vpi_get(vpiOpType, pattern), vpiAssignmentPatternOp);
  std::vector<std::string> names;
  vpiHandle it = vpi_iterate(vpiOperand, pattern);
  ASSERT_NE(it, nullptr);
  while (vpiHandle operand = vpi_scan(it)) {
    names.emplace_back(vpi_get_str(vpiName, operand));
  }
  EXPECT_EQ(names, (std::vector<std::string>{"x", "y"}));
}

TEST_F(ExpressionsOfARun, APositionalPatternIsAnAssignmentPatternOperation) {
  Run(std::string(kPairPrefix) + "  assign w = '{x, y}; endmodule\n");
  ExpectPatternOverXThenY(Rhs());
}

TEST_F(ExpressionsOfARun, AOneExpressionPatternIsAnAssignmentPatternOperation) {
  Run(std::string(kPairPrefix) + "  assign v = '{z}; endmodule\n");
  vpiHandle pattern = Rhs();
  ASSERT_NE(pattern, nullptr);
  EXPECT_EQ(vpi_get(vpiOpType, pattern), vpiAssignmentPatternOp);
  const std::vector<vpiHandle> kOperands = OperandsOf(pattern);
  ASSERT_EQ(kOperands.size(), 1U);
  EXPECT_STREQ(vpi_get_str(vpiName, kOperands[0]), "z");
}

TEST_F(ExpressionsOfARun,
       AReplicatedPatternIsAMultiAssignmentPatternOperation) {
  Run(std::string(kPairPrefix) + "  assign w = '{2 {y}}; endmodule\n");
  vpiHandle pattern = Rhs();
  ASSERT_NE(pattern, nullptr);
  EXPECT_EQ(vpi_get(vpiOpType, pattern), vpiMultiAssignmentPatternOp);
  const std::vector<vpiHandle> kOperands = OperandsOf(pattern);
  ASSERT_EQ(kOperands.size(), 2U);
  EXPECT_EQ(IntOf(kOperands[0]), 2);
  EXPECT_STREQ(vpi_get_str(vpiName, kOperands[1]), "y");
}

TEST_F(ExpressionsOfARun, AKeyedPatternTakesItsMembersOrder) {
  Run(std::string(kPairPrefix) +
      "  assign w = '{b: x, default: 1'b0};\n"
      "endmodule\n");
  vpiHandle pattern = Rhs();
  ASSERT_NE(pattern, nullptr);
  EXPECT_EQ(vpi_get(vpiOpType, pattern), vpiAssignmentPatternOp);
  const std::vector<vpiHandle> kOperands = OperandsOf(pattern);
  ASSERT_EQ(kOperands.size(), 2U);
  EXPECT_EQ(vpi_get(vpiType, kOperands[0]), vpiConstant);
  EXPECT_STREQ(vpi_get_str(vpiName, kOperands[1]), "x");
}

TEST_F(ExpressionsOfARun, AKeyedPatternNamingEveryMemberTakesTheirOrder) {
  Run(std::string(kPairPrefix) + "  assign w = '{b: y, a: x}; endmodule\n");
  ExpectPatternOverXThenY(Rhs());
}

std::vector<int> OperandValues(vpiHandle pattern) {
  std::vector<int> values;
  vpiHandle it =
      pattern == nullptr ? nullptr : vpi_iterate(vpiOperand, pattern);
  if (it == nullptr) return values;
  while (vpiHandle operand = vpi_scan(it)) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(operand, &value);
    values.push_back(value.value.integer);
  }
  return values;
}

TEST_F(ExpressionsOfARun, AKeyedPatternsTypeKeyFillsItsTypesMembers) {
  Run("module top;\n"
      "  typedef struct packed { int a; logic [3:0] b; int c; } mix_t;\n"
      "  mix_t w; assign w = '{c: 9, int: 7, default: 4'b0}; endmodule\n");
  EXPECT_EQ(OperandValues(Rhs()), (std::vector<int>{7, 0, 9}));
}

TEST_F(ExpressionsOfARun, AKeyedPatternsIndexKeyFillsItsElement) {
  Run("module top; logic [2:0] varr [0:3];\n"
      "  assign varr = '{3: 3'b1, default: 3'b0}; endmodule\n");
  EXPECT_EQ(OperandValues(Rhs()), (std::vector<int>{0, 0, 0, 1}));
}

TEST_F(ExpressionsOfARun, AProceduralKeyedPatternTakesItsMembersOrder) {
  Run(std::string(kPairPrefix) +
      "  initial w = '{b: x, default: 1'b0}; endmodule\n");
  vpiHandle procs = vpi_iterate(vpiProcess, By("top"));
  ASSERT_NE(procs, nullptr);
  vpiHandle assignment = vpi_handle(vpiStmt, vpi_scan(procs));
  ASSERT_NE(assignment, nullptr);
  vpiHandle pattern = vpi_handle(vpiRhs, assignment);
  ASSERT_NE(pattern, nullptr);
  EXPECT_EQ(vpi_get(vpiOpType, pattern), vpiAssignmentPatternOp);
  const std::vector<vpiHandle> kOperands = OperandsOf(pattern);
  ASSERT_EQ(kOperands.size(), 2U);
  EXPECT_EQ(vpi_get(vpiType, kOperands[0]), vpiConstant);
  EXPECT_STREQ(vpi_get_str(vpiName, kOperands[1]), "x");
}

void ExpectReplicationIsTheExpression(vpiHandle pattern) {
  ASSERT_NE(pattern, nullptr);
  EXPECT_EQ(vpi_get(vpiOpType, pattern), vpiAssignmentPatternOp);
  vpiHandle it = vpi_iterate(vpiOperand, pattern);
  ASSERT_NE(it, nullptr);
  vpiHandle operand = vpi_scan(it);
  ASSERT_NE(operand, nullptr);
  EXPECT_EQ(vpi_get(vpiOpType, operand), vpiMultiConcatOp);
  EXPECT_EQ(vpi_scan(it), nullptr);
}

TEST_F(ExpressionsOfARun, AReplicationOnAPatternsLineIsItsExpression) {
  Run(std::string(kPairPrefix) + "  assign v = '{ {2{y}} }; endmodule\n");
  ExpectReplicationIsTheExpression(Rhs());
}

TEST_F(ExpressionsOfARun, AReplicationBelowAPatternIsItsExpression) {
  Run(std::string(kPairPrefix) + "  assign v = '{\n {2{y}} }; endmodule\n");
  ExpectReplicationIsTheExpression(Rhs());
}

TEST(ExpressionModel, PartSelectParentOfBlankUnbalancedAndIndexedText) {
  EXPECT_EQ(VpiPartSelectParentExpr("  "), "");
  EXPECT_EQ(VpiPartSelectParentExpr("a]"), "");
  EXPECT_EQ(VpiPartSelectParentExpr("a[1]"), "a");
  EXPECT_EQ(VpiPartSelectParentExpr("a[b[1]]"), "a");
}

}  // namespace
}  // namespace delta
