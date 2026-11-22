#include <gtest/gtest.h>

#include <algorithm>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_simple_expr_uses.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

TEST(SimpleExpressionModel, VectorUseReachesVectorPartSelectsAndBitSelects) {
  EXPECT_TRUE(VpiSimpleExprVectorUseAccessesUse(true, false, false));
  EXPECT_TRUE(VpiSimpleExprVectorUseAccessesUse(false, true, false));
  EXPECT_TRUE(VpiSimpleExprVectorUseAccessesUse(false, false, true));
  EXPECT_FALSE(VpiSimpleExprVectorUseAccessesUse(false, false, false));
}

TEST(SimpleExpressionModel, BitSelectUseReachesBitParentAndContainingSelect) {
  EXPECT_TRUE(VpiSimpleExprBitSelectUseAccessesUse(true, false, false));
  EXPECT_TRUE(VpiSimpleExprBitSelectUseAccessesUse(false, true, false));
  EXPECT_TRUE(VpiSimpleExprBitSelectUseAccessesUse(false, false, true));
  EXPECT_FALSE(VpiSimpleExprBitSelectUseAccessesUse(false, false, false));
}

TEST(SimpleExpressionModel, BitSelectConstantSelectRequiresBothConditions) {
  EXPECT_TRUE(VpiSimpleExprBitSelectConstantSelect(true, true));

  EXPECT_FALSE(VpiSimpleExprBitSelectConstantSelect(false, true));

  EXPECT_FALSE(VpiSimpleExprBitSelectConstantSelect(true, false));

  EXPECT_FALSE(VpiSimpleExprBitSelectConstantSelect(false, false));
}

class BitSelectObject : public ::testing::Test {
 protected:
  void SetUp() override {
    SetGlobalVpiContext(&ctx_);
    vector_.type = vpiIntegerVar;
    index_.type = vpiConstant;
    select_.type = vpiBitSelect;
    select_.parent = &vector_;
    select_.children = {&index_};
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  std::vector<vpiHandle> ScanAll(vpiHandle it) {
    std::vector<vpiHandle> seen;
    if (it == nullptr) return seen;
    while (vpiHandle h = vpi_scan(it)) seen.push_back(h);
    return seen;
  }

  VpiObject vector_;
  VpiObject index_;
  VpiObject select_;
  VpiContext ctx_;
};

TEST_F(BitSelectObject, AConstantIndexIntoAStaticVectorIsAConstantSelect) {
  EXPECT_EQ(vpi_get(vpiConstantSelect, VpiHandleOf(&select_)), 1);
}

TEST_F(BitSelectObject, ANonConstantIndexMakesTheSelectNonConstant) {
  VpiObject variable;
  variable.type = vpiIntegerVar;
  index_.type = vpiOperation;
  index_.children = {&variable};

  EXPECT_EQ(vpi_get(vpiConstantSelect, VpiHandleOf(&select_)), 0);
}

TEST_F(BitSelectObject, AnAutomaticPrefixMakesTheSelectNonConstant) {
  vector_.automatic = true;

  EXPECT_EQ(vpi_get(vpiConstantSelect, VpiHandleOf(&select_)), 0);
}

TEST_F(BitSelectObject, ParentReachesTheVectorSelectedInto) {
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, VpiHandleOf(&select_))),
            &vector_);
}

TEST_F(BitSelectObject, IndexReachesTheSelectsIndexExpression) {
  std::vector<vpiHandle> seen =
      ScanAll(vpi_iterate(vpiIndex, VpiHandleOf(&select_)));
  ASSERT_EQ(seen.size(), 1u);
  EXPECT_EQ(VpiObjectOf(seen[0]), &index_);
}

class BitSelectsOfARun : public VpiDesignRun {
 protected:
  static int IntOf(vpiHandle obj) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(obj, &value);
    return value.value.integer;
  }

  static void PutInt(vpiHandle obj, int integer) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    value.value.integer = integer;
    vpi_put_value(obj, &value, nullptr, vpiNoDelay);
  }

  static vpiHandle Rhs() {
    vpiHandle it =
        vpi_iterate(vpiContAssign, vpi_handle_by_name(VpiText("top"), nullptr));
    if (it == nullptr) return nullptr;
    return vpi_handle(vpiRhs, vpi_scan(it));
  }
};

constexpr const char* kIntegerBit =
    "module top; integer i = 8; wire y; assign y = i[3]; endmodule\n";

TEST_F(BitSelectsOfARun, ABitOfAnIntegerIsABitSelect) {
  Run(kIntegerBit);
  EXPECT_EQ(vpi_get(vpiType, Rhs()), vpiBitSelect);
}

TEST_F(BitSelectsOfARun, ABitSelectsParentIsTheVariable) {
  Run(kIntegerBit);
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiParent, Rhs())), "i");
}

TEST_F(BitSelectsOfARun, ABitSelectsIndexIsTheWrittenIndex) {
  Run(kIntegerBit);
  EXPECT_EQ(IntOf(vpi_handle(vpiIndex, Rhs())), 3);
}

TEST_F(BitSelectsOfARun, ABitOfANetIsTheNetsBit) {
  Run("module top; wire [7:0] a; wire y; assign y = a[3]; endmodule\n");
  EXPECT_EQ(Rhs(), vpi_handle_by_index(
                       vpi_handle_by_name(VpiText("top.a"), nullptr), 3));
}

std::vector<vpiHandle> RightSides(vpiHandle scope) {
  std::vector<vpiHandle> sides;
  vpiHandle it = vpi_iterate(vpiContAssign, scope);
  if (it == nullptr) return sides;
  for (vpiHandle ca = vpi_scan(it); ca != nullptr; ca = vpi_scan(it)) {
    sides.push_back(vpi_handle(vpiRhs, ca));
  }
  return sides;
}

TEST_F(BitSelectsOfARun, AParameterIndexChoosesTheNetsOwnBit) {
  Run("module top; parameter P = 4; wire [7:0] a; wire y, z;\n"
      "assign y = a[P]; assign z = a[P-1];\n"
      "endmodule\n");
  const std::vector<vpiHandle> kSides = RightSides(By("top"));
  ASSERT_EQ(kSides.size(), 2U);
  EXPECT_EQ(kSides[0], vpi_handle_by_index(By("top.a"), 4));
  EXPECT_EQ(kSides[1], vpi_handle_by_index(By("top.a"), 3));
  EXPECT_EQ(vpi_get(vpiConstantSelect, kSides[0]), 1);
}

TEST_F(BitSelectsOfARun, AGenvarIndexChoosesTheNetsOwnBit) {
  Run("module top; wire [7:0] a;\n"
      "  for (genvar g = 2; g < 4; g++) begin : gb\n"
      "    wire y; assign y = a[g];\n"
      "  end\n"
      "endmodule\n");
  const std::vector<vpiHandle> kSides = RightSides(By("top.gb[3]"));
  ASSERT_EQ(kSides.size(), 1U);
  EXPECT_EQ(kSides[0], vpi_handle_by_index(By("top.a"), 3));
}

TEST_F(BitSelectsOfARun, AParameterIndexChoosesTheArraysElement) {
  Run("module top; parameter P = 1; logic [7:0] arr [0:3]; wire [7:0] y;\n"
      "assign y = arr[P];\n"
      "endmodule\n");
  EXPECT_EQ(Rhs(), vpi_handle_by_index(By("top.arr"), 1));
}

TEST_F(BitSelectsOfARun, AParameterIndexedBitSelectIsAConstantSelect) {
  Run("module top; parameter P = 4; integer i, k; wire a, b, c;\n"
      "assign a = i[P]; assign b = i[P-1]; assign c = i[k+1];\n"
      "endmodule\n");
  const std::vector<vpiHandle> kSides = RightSides(By("top"));
  ASSERT_EQ(kSides.size(), 3U);
  EXPECT_EQ(vpi_get(vpiType, kSides[0]), vpiBitSelect);
  EXPECT_EQ(vpi_get(vpiConstantSelect, kSides[0]), 1);
  EXPECT_EQ(vpi_get(vpiConstantSelect, kSides[1]), 1);
  EXPECT_EQ(vpi_get(vpiConstantSelect, kSides[2]), 0);
}

TEST_F(BitSelectsOfARun, AParameterBoundedPartSelectIsAConstantSelect) {
  Run("module top; parameter P = 4; wire [7:0] n; integer k;\n"
      "wire [2:0] a; wire [3:0] b, c;\n"
      "assign a = n[P:2]; assign b = n[2+:P]; assign c = n[k+:P];\n"
      "endmodule\n");
  const std::vector<vpiHandle> kSides = RightSides(By("top"));
  ASSERT_EQ(kSides.size(), 3U);
  EXPECT_EQ(vpi_get(vpiType, kSides[0]), vpiPartSelect);
  EXPECT_EQ(vpi_get(vpiConstantSelect, kSides[0]), 1);
  EXPECT_EQ(vpi_get(vpiConstantSelect, kSides[1]), 1);
  EXPECT_EQ(vpi_get(vpiConstantSelect, kSides[2]), 0);
}

constexpr const char* kVaryingNetBit =
    "module top; wire [7:0] a; integer i = 2; wire y; assign y = a[i];\n"
    "endmodule\n";

TEST_F(BitSelectsOfARun, AVaryingBitOfANetIsANetBit) {
  Run(kVaryingNetBit);
  EXPECT_EQ(vpi_get(vpiType, Rhs()), vpiNetBit);
}

TEST_F(BitSelectsOfARun, AVaryingBitsParentIsTheNet) {
  Run(kVaryingNetBit);
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiParent, Rhs())), "a");
}

TEST_F(BitSelectsOfARun, AVaryingBitsIndexIsTheWrittenIndex) {
  Run(kVaryingNetBit);
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiIndex, Rhs())), "i");
}

TEST_F(BitSelectsOfARun, AVaryingBitIsNoConstantSelect) {
  Run(kVaryingNetBit);
  EXPECT_EQ(vpi_get(vpiConstantSelect, Rhs()), 0);
}

TEST_F(BitSelectsOfARun, AVaryingBitOfAVariableIsAVarBit) {
  Run("module top; logic [7:0] v; integer i = 2; wire y; assign y = v[i];\n"
      "endmodule\n");
  EXPECT_EQ(vpi_get(vpiType, Rhs()), vpiRegBit);
}

constexpr const char* kVaryingVarBit =
    "module top; logic [7:0] v = 8'b0000_0100; integer i = 2; wire y;\n"
    "assign y = v[i];\n"
    "endmodule\n";

TEST_F(BitSelectsOfARun, AVaryingBitHoldsTheBitItsIndexSelects) {
  Run(kVaryingVarBit);
  EXPECT_EQ(IntOf(Rhs()), 1);
}

TEST_F(BitSelectsOfARun, AVaryingBitFollowsItsIndex) {
  Run(kVaryingVarBit);
  PutInt(vpi_handle_by_name(VpiText("top.i"), nullptr), 4);
  EXPECT_EQ(IntOf(Rhs()), 0);
}

TEST_F(BitSelectsOfARun, AVaryingBitPastTheRangeReadsX) {
  Run(kVaryingVarBit);
  PutInt(vpi_handle_by_name(VpiText("top.i"), nullptr), 9);
  s_vpi_value value = {};
  value.format = vpiScalarVal;
  vpi_get_value(Rhs(), &value);
  EXPECT_EQ(value.value.scalar, vpiX);
}

TEST_F(BitSelectsOfARun, WritingAVaryingBitWritesTheBitItsIndexSelects) {
  Run(kVaryingVarBit);
  PutInt(vpi_handle_by_name(VpiText("top.i"), nullptr), 0);
  PutInt(Rhs(), 1);
  EXPECT_EQ(IntOf(vpi_handle_by_name(VpiText("top.v"), nullptr)), 5);
}

TEST_F(BitSelectsOfARun, AVaryingBitOfANetHoldsTheBitItsIndexSelects) {
  Run("module top; wire [7:0] a; integer i = 2; wire y; assign y = a[i];\n"
      "assign a = 8'b0000_0100;\n"
      "endmodule\n");
  EXPECT_EQ(IntOf(Rhs()), 1);
}

TEST_F(BitSelectsOfARun, ABitSelectByAVariableIsNoConstantSelect) {
  Run("module top; integer i, j; wire w; assign w = i[j]; endmodule\n");
  EXPECT_EQ(vpi_get(vpiConstantSelect, Rhs()), 0);
}

TEST_F(BitSelectsOfARun, ABitSelectByAConstantIsAConstantSelect) {
  Run(kIntegerBit);
  EXPECT_EQ(vpi_get(vpiConstantSelect, Rhs()), 1);
}

TEST_F(BitSelectsOfARun, ABitSelectIsNamedByItsParentAndIndex) {
  Run(kIntegerBit);
  EXPECT_STREQ(vpi_get_str(vpiName, Rhs()), "i[3]");
}

TEST_F(BitSelectsOfARun, ABitSelectsFullNameIsItsParents) {
  Run(kIntegerBit);
  EXPECT_STREQ(vpi_get_str(vpiFullName, Rhs()), "top.i[3]");
}

constexpr const char* kElementBit =
    "module top; logic [7:0] arr [0:3]; wire y; assign y = arr[1][3];\n"
    "endmodule\n";

TEST_F(BitSelectsOfARun, ABitOfAnElementIsTheElementsVarBit) {
  Run(kElementBit);
  vpiHandle element = vpi_handle_by_index(By("top.arr"), 1);
  ASSERT_NE(element, nullptr);
  EXPECT_EQ(vpi_get(vpiType, Rhs()), vpiRegBit);
  EXPECT_EQ(Rhs(), vpi_handle_by_index(element, 3));
}

TEST_F(BitSelectsOfARun, AnElementsBitsAreNoIndicesOfIt) {
  Run(kElementBit);
  vpiHandle element = vpi_handle_by_index(By("top.arr"), 1);
  ASSERT_NE(element, nullptr);
  vpiHandle it = vpi_iterate(vpiIndex, element);
  ASSERT_NE(it, nullptr);
  int count = 0;
  while (vpi_scan(it) != nullptr) ++count;
  EXPECT_EQ(count, 1);
}

std::vector<int> PropertyOfUses(int property, vpiHandle expr) {
  std::vector<int> values;
  vpiHandle it = vpi_iterate(vpiUse, expr);
  if (it == nullptr) return values;
  for (vpiHandle use = vpi_scan(it); use != nullptr; use = vpi_scan(it)) {
    values.push_back(vpi_get(property, use));
  }
  std::ranges::sort(values);
  return values;
}

std::vector<int> LinesOfUses(vpiHandle expr) {
  return PropertyOfUses(vpiLineNo, expr);
}

std::vector<int> KindsOfUses(vpiHandle expr) {
  return PropertyOfUses(vpiType, expr);
}

std::vector<int> Ascending(std::vector<int> kinds) {
  std::ranges::sort(kinds);
  return kinds;
}

TEST_F(BitSelectsOfARun, AVectorIsUsedWhereItOrASelectOfItIs) {
  Run("module top; logic [7:0] v; wire a, b, c; logic [7:0] w;\n"
      "assign a = v[2];\n"
      "assign b = c;\n"
      "assign c = |v[5:4];\n"
      "initial w = v;\n"
      "endmodule\n");
  EXPECT_EQ(LinesOfUses(By("top.v")), (std::vector<int>{2, 4, 5}));
  const std::vector<vpiHandle> kSides = RightSides(By("top"));
  ASSERT_EQ(kSides.size(), 3U);
  ASSERT_EQ(vpi_get(vpiType, kSides[2]), vpiOperation);
  EXPECT_EQ(vpi_iterate(vpiUse, kSides[2]), nullptr);
}

TEST_F(BitSelectsOfARun, ABitIsUsedWhereItItsVectorOrASelectHoldingItIs) {
  Run("module top; integer i, j; wire a, b, c, d;\n"
      "assign a = i[3];\n"
      "assign b = i[3];\n"
      "assign c = i[5];\n"
      "assign d = ^i[4:2];\n"
      "initial j = i;\n"
      "endmodule\n");
  EXPECT_EQ(LinesOfUses(Rhs()), (std::vector<int>{2, 3, 5, 6}));
}

TEST_F(BitSelectsOfARun, AVectorIsUsedThroughEverySelectKindAndAnIndex) {
  Run("module top; integer i; logic [7:0] v; wire [3:0] n;\n"
      "logic [7:0] arr [0:3]; wire a, b, c, y;\n"
      "assign a = i[3];\n"
      "assign b = ^v[2+:2];\n"
      "assign c = n[1] | v[i];\n"
      "assign y = ^arr[i];\n"
      "endmodule\n");
  EXPECT_EQ(LinesOfUses(By("top.i")), (std::vector<int>{3, 5, 6}));
  EXPECT_EQ(LinesOfUses(By("top.v")), (std::vector<int>{4, 5}));
  EXPECT_EQ(LinesOfUses(By("top.n")), (std::vector<int>{5}));
  EXPECT_EQ(LinesOfUses(By("top.arr")), (std::vector<int>{6}));
}

TEST_F(BitSelectsOfARun, ANetBitIsUsedWhereASelectsBoundsHoldIt) {
  Run("module top; wire [7:0] n; wire a, b, c, d, e, f;\n"
      "assign a = n[3];\n"
      "assign b = ^n[5:2];\n"
      "assign c = ^n[2+:2];\n"
      "assign d = ^n[4-:2];\n"
      "assign e = ^n[2:0];\n"
      "assign f = ^n[6:4];\n"
      "endmodule\n");
  EXPECT_EQ(vpi_get(vpiType, Rhs()), vpiNetBit);
  EXPECT_EQ(LinesOfUses(Rhs()), (std::vector<int>{2, 3, 4, 5}));
}

TEST_F(BitSelectsOfARun, ANetBitIsUsedWhereAParameterBoundedSelectHoldsIt) {
  Run("module top; parameter P = 4; wire [7:0] n; integer k;\n"
      "wire a, b, c, d, e; assign a = n[3];\n"
      "assign b = ^n[P:2];\n"
      "assign c = ^n[2+:P];\n"
      "assign d = ^n[P+:2];\n"
      "assign e = n[k];\n"
      "endmodule\n");
  EXPECT_EQ(LinesOfUses(Rhs()), (std::vector<int>{2, 3, 4}));
}

TEST_F(BitSelectsOfARun, ANetBitIsUsedWhereAGenvarBasedSelectHoldsIt) {
  Run("module top; wire [7:0] n; wire a;\n"
      "assign a = n[3];\n"
      "for (genvar g = 2; g < 5; g += 2) begin : blk\n"
      "  wire b;\n"
      "  assign b = ^n[g+:2];\n"
      "end\n"
      "endmodule\n");
  EXPECT_EQ(LinesOfUses(Rhs()), (std::vector<int>{2, 5}));
}

TEST(SimpleExpressionModel, ABitMatchesASelectOnlyByConstantValues) {
  Arena arena;
  Variable three_value;
  three_value.value = MakeLogic4VecVal(arena, 32, 3);
  VpiObject three;
  three.type = vpiConstant;
  three.var = &three_value;
  VpiObject valueless;
  valueless.type = vpiConstant;
  VpiObject vector;
  vector.type = vpiLogicVar;
  const auto kSelectOf = [&vector](int type) {
    VpiObject select;
    select.type = type;
    select.parent = &vector;
    return select;
  };

  VpiObject bit = kSelectOf(vpiRegBit);
  bit.index_expr = &three;
  VpiObject twin = kSelectOf(vpiRegBit);
  twin.index_expr = &three;
  EXPECT_TRUE(VpiExpressionUses(&twin, bit));
  VpiObject spec_three;
  spec_three.type = vpiSpecParam;
  spec_three.var = &three_value;
  VpiObject spec_twin = kSelectOf(vpiRegBit);
  spec_twin.index_expr = &spec_three;
  EXPECT_TRUE(VpiExpressionUses(&spec_twin, bit));
  VpiObject no_value = kSelectOf(vpiRegBit);
  no_value.index_expr = &valueless;
  EXPECT_FALSE(VpiExpressionUses(&no_value, bit));
  VpiObject no_index = kSelectOf(vpiRegBit);
  EXPECT_FALSE(VpiExpressionUses(&bit, no_index));

  VpiObject no_left = kSelectOf(vpiPartSelect);
  no_left.right_range = &three;
  EXPECT_FALSE(VpiExpressionUses(&no_left, bit));
  VpiObject no_right = kSelectOf(vpiPartSelect);
  no_right.left_range = &three;
  EXPECT_FALSE(VpiExpressionUses(&no_right, bit));
  VpiObject no_base = kSelectOf(vpiIndexedPartSelect);
  no_base.width_expr = &three;
  EXPECT_FALSE(VpiExpressionUses(&no_base, bit));
  VpiObject no_width = kSelectOf(vpiIndexedPartSelect);
  no_width.base_expr = &three;
  EXPECT_FALSE(VpiExpressionUses(&no_width, bit));
}

constexpr const char* kTimedCell =
    "module m(input a, input c, output y);\n"
    "  buf g(y, a);\n"
    "  specify (a => y) = 3; $setup(a, posedge c, 1); endspecify\n"
    "endmodule\n"
    "module top; wire p, q, r; wire [1:0] w; assign w = 2'b01;\n"
    "  m u(p, r, q);\n"
    "endmodule\n";

TEST_F(BitSelectsOfARun, AWireIsUsedByThePortItConnectsAlone) {
  Run(kTimedCell);
  vpiHandle it = vpi_iterate(vpiUse, By("top.p"));
  ASSERT_NE(it, nullptr);
  vpiHandle use = vpi_scan(it);
  ASSERT_NE(use, nullptr);
  EXPECT_EQ(vpi_get(vpiType, use), vpiPort);
  EXPECT_STREQ(vpi_get_str(vpiName, use), "a");
  EXPECT_EQ(vpi_scan(it), nullptr);
}

TEST_F(BitSelectsOfARun, ACellInputIsUsedByItsPathAndTimingCheckTerms) {
  Run(kTimedCell);
  EXPECT_EQ(KindsOfUses(By("top.u.a")),
            Ascending({vpiPort, vpiPrimTerm, vpiPathTerm, vpiTchkTerm}));
}

TEST_F(BitSelectsOfARun, ACellOutputIsUsedByItsPathDevicesDelayTerms) {
  Run(kTimedCell);
  EXPECT_EQ(KindsOfUses(By("top.u.y")),
            Ascending({vpiPort, vpiPrimTerm, vpiPathTerm, vpiDelayTerm,
                       vpiDelayTerm}));
}

TEST_F(BitSelectsOfARun, AnAssignmentsBitsUseWhatTheAssignmentUses) {
  Run("module top; logic [1:0] v; wire [1:0] w; assign w = v; endmodule\n");
  EXPECT_EQ(KindsOfUses(By("top.v")),
            Ascending({vpiContAssign, vpiContAssignBit, vpiContAssignBit}));
}

TEST(SimpleExpressionModel, AnAssignmentBitOfNoAssignmentUsesNothing) {
  VpiObject net;
  net.type = vpiNet;
  VpiObject bit;
  bit.type = vpiContAssignBit;
  EXPECT_FALSE(VpiUsesExpr(bit, net));
}

TEST(SimpleExpressionModel, TheSimpleExpressionsAreTheFiguresKinds) {
  EXPECT_FALSE(VpiIsSimpleExpr(nullptr));
  for (int type :
       {vpiRefObj, vpiParameter, vpiSpecParam, vpiVarSelect, vpiBitSelect,
        vpiNet, vpiNetBit, vpiLogicVar, vpiIntegerVar}) {
    VpiObject obj;
    obj.type = type;
    EXPECT_TRUE(VpiIsSimpleExpr(&obj)) << type;
  }
  for (int type : {vpiPartSelect, vpiOperation, vpiConstant, vpiModule}) {
    VpiObject obj;
    obj.type = type;
    EXPECT_FALSE(VpiIsSimpleExpr(&obj)) << type;
  }
}

TEST(SimpleExpressionModel, ASelectOrBitOfNothingIsUsedOnlyWhereItStands) {
  VpiObject vector;
  vector.type = vpiLogicVar;
  VpiObject select;
  select.type = vpiPartSelect;
  EXPECT_FALSE(VpiExpressionUses(&select, vector));

  VpiObject bit;
  bit.type = vpiBitSelect;
  VpiObject other;
  other.type = vpiBitSelect;
  EXPECT_FALSE(VpiExpressionUses(&other, bit));
  EXPECT_TRUE(VpiExpressionUses(&bit, bit));
}

TEST_F(BitSelectObject, ABitResolvesOnlyItsIndexAndParent) {
  VpiObject net;
  net.type = vpiNet;
  VpiObject bit;
  bit.type = vpiNetBit;
  bit.parent = &net;
  VpiHandle out = nullptr;
  EXPECT_FALSE(TryResolveSelectRelation(vpiExpr, &bit, out));
  EXPECT_EQ(out, nullptr);
}

TEST(BitSelectConstantSelect, ReadOffTheSelectAndItsParent) {
  EXPECT_FALSE(VpiBitSelectConstantSelectOf(nullptr));
  VpiObject ref;
  ref.type = vpiRefObj;
  EXPECT_FALSE(VpiBitSelectConstantSelectOf(&ref));

  VpiObject attribute;
  attribute.type = vpiAttribute;
  VpiObject index;
  index.type = vpiConstant;
  VpiObject orphan;
  orphan.type = vpiBitSelect;
  orphan.children = {&attribute, &index};
  EXPECT_FALSE(VpiBitSelectConstantSelectOf(&orphan));

  VpiObject var;
  var.type = vpiIntegerVar;
  VpiObject inner;
  inner.type = vpiBitSelect;
  inner.parent = &var;
  inner.children = {&index};
  VpiObject outer;
  outer.type = vpiBitSelect;
  outer.parent = &inner;
  outer.children = {&index};
  EXPECT_TRUE(VpiBitSelectConstantSelectOf(&outer));

  VpiObject var_select;
  var_select.type = vpiVarSelect;
  VpiObject of_var_select;
  of_var_select.type = vpiBitSelect;
  of_var_select.parent = &var_select;
  of_var_select.children = {&index};
  EXPECT_EQ(VpiBitSelectConstantSelectOf(&of_var_select),
            VpiVarSelectConstantSelectOf(&var_select));
}
TEST(SimpleExpressionModel, ElaborationConstantsAreConstantsAndParameters) {
  EXPECT_FALSE(VpiIsElaborationConstant(nullptr));
  VpiObject spec;
  spec.type = vpiSpecParam;
  EXPECT_TRUE(VpiIsElaborationConstant(&spec));
  VpiObject attribute;
  attribute.type = vpiAttribute;
  VpiObject operation;
  operation.type = vpiOperation;
  operation.children = {&spec, &attribute};
  EXPECT_TRUE(VpiIsElaborationConstant(&operation));
  VpiObject var;
  var.type = vpiIntegerVar;
  EXPECT_FALSE(VpiIsElaborationConstant(&var));
  operation.children.push_back(&var);
  EXPECT_FALSE(VpiIsElaborationConstant(&operation));
}

class ConstantsOfARun : public VpiDesignRun {};

TEST_F(ConstantsOfARun, ATimeLiteralIsATimeConstant) {
  Run("module top; timeunit 1ns; timeprecision 1ps;\n"
      "  realtime r; assign r = 2.5ns; endmodule\n");
  vpiHandle it = vpi_iterate(vpiContAssign, By("top"));
  ASSERT_NE(it, nullptr);
  vpiHandle literal = vpi_handle(vpiRhs, vpi_scan(it));
  ASSERT_NE(literal, nullptr);
  EXPECT_EQ(vpi_get(vpiType, literal), vpiConstant);
  EXPECT_EQ(vpi_get(vpiConstType, literal), vpiTimeConst);
  s_vpi_value value = {};
  value.format = vpiRealVal;
  vpi_get_value(literal, &value);
  EXPECT_DOUBLE_EQ(value.value.real, 2.5);
}

}  // namespace
}  // namespace delta
