#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

TEST(SequenceExprModel, ClassGroupsItsMemberKinds) {
  EXPECT_TRUE(VpiIsSequenceExprType(vpiOperation));
  EXPECT_TRUE(VpiIsSequenceExprType(vpiSequenceInst));
  EXPECT_TRUE(VpiIsSequenceExprType(vpiDistribution));
  EXPECT_TRUE(VpiIsSequenceExprType(vpiConstant));
  EXPECT_TRUE(VpiIsSequenceExprType(vpiRefObj));

  EXPECT_FALSE(VpiIsSequenceExprType(vpiModule));
  EXPECT_FALSE(VpiIsSequenceExprType(vpiNet));
  EXPECT_FALSE(VpiIsSequenceExprType(vpiClockingBlock));
}

TEST(SequenceExprModel, OpTypeSetCoversTheElevenSequenceOperators) {
  for (int op :
       {vpiCompAndOp, vpiIntersectOp, vpiCompOrOp, vpiFirstMatchOp,
        vpiThroughoutOp, vpiWithinOp, vpiUnaryCycleDelayOp, vpiCycleDelayOp,
        vpiRepeatOp, vpiConsecutiveRepeatOp, vpiGotoRepeatOp}) {
    EXPECT_TRUE(VpiIsSequenceExprOpType(op)) << "op=" << op;
  }
}

TEST(SequenceExprModel, OperationReportsItsOpTypeProperty) {
  VpiContext ctx;
  VpiObject op;
  op.type = vpiOperation;
  op.op_type = vpiThroughoutOp;

  EXPECT_EQ(ctx.Get(vpiOpType, &op), vpiThroughoutOp);
  EXPECT_TRUE(VpiIsSequenceExprOpType(ctx.Get(vpiOpType, &op)));

  VpiObject unset;
  unset.type = vpiOperation;
  EXPECT_EQ(ctx.Get(vpiOpType, &unset), 0);
}

TEST(SequenceExprModel, OpTypeSetRejectsNonSequenceOperators) {
  EXPECT_FALSE(VpiIsSequenceExprOpType(vpiAddOp));
  EXPECT_FALSE(VpiIsSequenceExprOpType(vpiLogAndOp));
  EXPECT_FALSE(VpiIsSequenceExprOpType(vpiImplyOp));
  EXPECT_FALSE(VpiIsSequenceExprOpType(vpiUntilOp));
}

TEST(SequenceExprModel, UnaryCycleDelayOperandOrderAndRangeOmission) {
  VpiObject seq;
  VpiObject lo;
  VpiObject hi;

  auto with_range = VpiUnaryCycleDelayOperands(&seq, &lo, &hi);
  ASSERT_EQ(with_range.size(), 3u);
  EXPECT_EQ(with_range[0], &seq);
  EXPECT_EQ(with_range[1], &lo);
  EXPECT_EQ(with_range[2], &hi);

  auto eq_range = VpiUnaryCycleDelayOperands(&seq, &lo, &lo);
  ASSERT_EQ(eq_range.size(), 2u);
  EXPECT_EQ(eq_range[0], &seq);
  EXPECT_EQ(eq_range[1], &lo);

  auto no_right = VpiUnaryCycleDelayOperands(&seq, &lo, nullptr);
  ASSERT_EQ(no_right.size(), 2u);
  EXPECT_EQ(no_right[1], &lo);
}

TEST(SequenceExprModel, CycleDelayOperandOrderAndRangeOmission) {
  VpiObject lhs;
  VpiObject rhs;
  VpiObject lo;
  VpiObject hi;

  auto full = VpiCycleDelayOperands(&lhs, &rhs, &lo, &hi);
  ASSERT_EQ(full.size(), 4u);
  EXPECT_EQ(full[0], &lhs);
  EXPECT_EQ(full[1], &rhs);
  EXPECT_EQ(full[2], &lo);
  EXPECT_EQ(full[3], &hi);

  auto eq = VpiCycleDelayOperands(&lhs, &rhs, &lo, &lo);
  ASSERT_EQ(eq.size(), 3u);
  EXPECT_EQ(eq[0], &lhs);
  EXPECT_EQ(eq[1], &rhs);
  EXPECT_EQ(eq[2], &lo);

  auto no_right = VpiCycleDelayOperands(&lhs, &rhs, &lo, nullptr);
  ASSERT_EQ(no_right.size(), 3u);
  EXPECT_EQ(no_right[2], &lo);
}

TEST(SequenceExprModel, RepeatOperandOrderAndBoundOmission) {
  VpiObject seq;
  VpiObject lo;
  VpiObject hi;

  auto full = VpiRepeatOperands(&seq, &lo, &hi);
  ASSERT_EQ(full.size(), 3u);
  EXPECT_EQ(full[0], &seq);
  EXPECT_EQ(full[1], &lo);
  EXPECT_EQ(full[2], &hi);

  auto single = VpiRepeatOperands(&seq, &lo, &lo);
  ASSERT_EQ(single.size(), 2u);
  EXPECT_EQ(single[0], &seq);
  EXPECT_EQ(single[1], &lo);

  auto no_right = VpiRepeatOperands(&seq, &lo, nullptr);
  ASSERT_EQ(no_right.size(), 2u);
}

TEST(SequenceExprModel, ArgumentsFollowFormalOrderAndFillDefaults) {
  VpiObject a0;
  VpiObject a2;
  VpiObject def1;

  std::vector<VpiSequenceFormal> formals = {
      {nullptr},
      {&def1},
      {nullptr},
  };
  std::vector<VpiHandle> provided = {&a0, nullptr, &a2};

  auto args = VpiSequenceInstArguments(formals, provided);
  ASSERT_EQ(args.size(), 3u);
  EXPECT_EQ(args[0], &a0);
  EXPECT_EQ(args[1], &def1);
  EXPECT_EQ(args[2], &a2);
}

TEST(SequenceExprModel, ArgumentsUseSuppliedActualsOverDefaults) {
  VpiObject a0;
  VpiObject a1;
  VpiObject def1;

  std::vector<VpiSequenceFormal> formals = {{nullptr}, {&def1}};
  std::vector<VpiHandle> provided = {&a0, &a1};

  auto args = VpiSequenceInstArguments(formals, provided);
  ASSERT_EQ(args.size(), 2u);
  EXPECT_EQ(args[0], &a0);
  EXPECT_EQ(args[1], &a1);
}

TEST(SequenceExprModel, OmittedFormalWithoutDefaultYieldsNoArgument) {
  VpiObject a0;

  std::vector<VpiSequenceFormal> formals = {{nullptr}, {nullptr}};
  std::vector<VpiHandle> provided = {&a0, nullptr};

  auto args = VpiSequenceInstArguments(formals, provided);
  ASSERT_EQ(args.size(), 2u);
  EXPECT_EQ(args[0], &a0);
  EXPECT_EQ(args[1], nullptr);
}

TEST(SequenceExprModel, TrailingFormalsBeyondProvidedUseDefaults) {
  VpiObject a0;
  VpiObject def1;

  std::vector<VpiSequenceFormal> formals = {{nullptr}, {&def1}};
  std::vector<VpiHandle> provided = {&a0};

  auto args = VpiSequenceInstArguments(formals, provided);
  ASSERT_EQ(args.size(), 2u);
  EXPECT_EQ(args[0], &a0);
  EXPECT_EQ(args[1], &def1);
}

TEST(SequenceExprModel, SequenceArgumentKindsAreNamedEventOrSequenceExpr) {
  EXPECT_TRUE(VpiIsSequenceArgumentType(vpiNamedEvent));
  EXPECT_TRUE(VpiIsSequenceArgumentType(vpiSequenceInst));
  EXPECT_TRUE(VpiIsSequenceArgumentType(vpiOperation));
  EXPECT_TRUE(VpiIsSequenceArgumentType(vpiConstant));

  EXPECT_FALSE(VpiIsSequenceArgumentType(vpiNet));
  EXPECT_FALSE(VpiIsSequenceArgumentType(vpiModule));
}

TEST(SequenceExprModel, SequenceInstResolvesItsDeclaration) {
  VpiObject inst;
  inst.type = vpiSequenceInst;
  VpiObject decl;
  decl.type = vpiSequenceDecl;
  inst.sequence_decl = &decl;
  EXPECT_EQ(VpiSequenceInstDecl(&inst), &decl);

  VpiObject lone;
  lone.type = vpiSequenceInst;
  EXPECT_EQ(VpiSequenceInstDecl(&lone), nullptr);
  EXPECT_EQ(VpiSequenceInstDecl(nullptr), nullptr);
}

TEST(SequenceExprModel, SequenceInstWithADeclChildResolvesNone) {
  VpiObject inst;
  inst.type = vpiSequenceInst;
  VpiObject decl;
  decl.type = vpiSequenceDecl;
  VpiObject operand;
  operand.type = vpiOperation;
  inst.children = {&decl, &operand};

  EXPECT_EQ(VpiSequenceInstDecl(&inst), nullptr);
}

TEST(SequenceExprModel, MatchItemKindsAreAssignmentsAndTfCalls) {
  EXPECT_TRUE(VpiIsMatchItemType(vpiAssignment));
  EXPECT_TRUE(VpiIsMatchItemType(vpiFuncCall));
  EXPECT_TRUE(VpiIsMatchItemType(vpiTaskCall));

  EXPECT_FALSE(VpiIsMatchItemType(vpiNet));
  EXPECT_FALSE(VpiIsMatchItemType(vpiOperation));
}

TEST(SequenceExprModel, MatchItemsCollectAssignmentAndTfCallChildren) {
  VpiObject expr;
  VpiObject assign;
  assign.type = vpiAssignment;
  VpiObject call;
  call.type = vpiTaskCall;
  VpiObject other;
  other.type = vpiOperation;
  expr.children = {&assign, &other, &call};

  auto items = VpiExprMatchItems(&expr);
  ASSERT_EQ(items.size(), 2u);
  EXPECT_EQ(items[0], &assign);
  EXPECT_EQ(items[1], &call);

  EXPECT_TRUE(VpiExprMatchItems(nullptr).empty());
}

constexpr const char* kSequenceOperators =
    "module top; logic clk, a, b, c, d;\n"
    "  struct packed { logic f; } st;\n"
    "  d1: assert property (@(posedge clk) a ##1 b);\n"
    "  d2: assert property (@(posedge clk) a ##[1:3] b);\n"
    "  d3: assert property (@(posedge clk) ##2 a);\n"
    "  d4: assert property (@(posedge clk) ##0 a);\n"
    "  sequence s(x, y = c); x ##1 y; endsequence\n"
    "  sequence u; a; endsequence\n"
    "  i1: assert property (@(posedge clk) s(a) ##1 b);\n"
    "  i2: assert property (@(posedge clk) u);\n"
    "  e1: assert property (@(posedge clk) st.f ##1 b);\n"
    "  x1: assert property (@(posedge clk) a dist {0 := 1, 1 := 3} ##1 b);\n"
    "  x2: assert property (@(posedge clk) a dist {1 := 3, default :/ 1} ##1 "
    "b);\n"
    "  r1: assert property (@(posedge clk) a[*2] ##1 b);\n"
    "  r2: assert property (@(posedge clk) a[->1:2] ##1 b);\n"
    "  r3: assert property (@(posedge clk) a[=3] ##1 b);\n"
    "  j1: assert property (@(posedge clk) (a ##1 b) intersect (c ##1 d));\n"
    "  m1: assert property (@(posedge clk) first_match(a ##[1:2] b));\n"
    "  p1: assert property (@(posedge clk) a ##1 b |-> c);\n"
    "  t1: assert property (@(posedge clk) a throughout (b ##1 c));\n"
    "  w1: assert property (@(posedge clk) (a ##1 b) within (c ##3 d));\n"
    "  property q;\n"
    "    int n;\n"
    "    @(posedge clk) (a, n = 1, n += 2) ##1 b;\n"
    "  endproperty\n"
    "  property q2;\n"
    "    logic [7:0] v;\n"
    "    @(posedge clk) (a, v[3:2] = 2'b11) ##1 b;\n"
    "  endproperty\n"
    "endmodule\n";

class SequenceExprsOfARun : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    Run(kSequenceOperators);
  }

  static std::vector<std::string> Spelled(vpiHandle op) {
    std::vector<std::string> spelled;
    for (vpiHandle operand : OperandsOf(op)) {
      const int kType = vpi_get(vpiType, operand);
      if (kType == vpiOperation) {
        spelled.emplace_back("op");
      } else if (kType == vpiConstant) {
        s_vpi_value value = {};
        value.format = vpiIntVal;
        vpi_get_value(operand, &value);
        spelled.push_back(std::to_string(value.value.integer));
      } else {
        const char* name = vpi_get_str(vpiName, operand);
        spelled.emplace_back(name == nullptr ? "" : name);
      }
    }
    return spelled;
  }
};

TEST_F(SequenceExprsOfARun, CycleDelaysTakeTheirRanges) {
  EXPECT_EQ(OpOf(PropertyOf("d1")), vpiCycleDelayOp);
  EXPECT_EQ(Spelled(PropertyOf("d1")),
            (std::vector<std::string>{"a", "b", "1"}));
  EXPECT_EQ(Spelled(PropertyOf("d2")),
            (std::vector<std::string>{"a", "b", "1", "3"}));
  EXPECT_EQ(OpOf(PropertyOf("d3")), vpiUnaryCycleDelayOp);
  EXPECT_EQ(Spelled(PropertyOf("d3")), (std::vector<std::string>{"a", "2"}));
}

TEST_F(SequenceExprsOfARun, ALeadingZeroDelayIsAUnaryCycleDelay) {
  EXPECT_EQ(OpOf(PropertyOf("d4")), vpiUnaryCycleDelayOp);
  EXPECT_EQ(Spelled(PropertyOf("d4")), (std::vector<std::string>{"a", "0"}));
}

TEST_F(SequenceExprsOfARun, ANamedSequenceIsASequenceInst) {
  vpiHandle chain = PropertyOf("i1");
  EXPECT_EQ(OpOf(chain), vpiCycleDelayOp);
  const std::vector<vpiHandle> kParts = OperandsOf(chain);
  ASSERT_EQ(kParts.size(), 3u);
  vpiHandle inst = kParts[0];
  EXPECT_EQ(vpi_get(vpiType, inst), vpiSequenceInst);
  vpiHandle decl = vpi_handle(vpiSequenceDecl, inst);
  ASSERT_NE(decl, nullptr);
  EXPECT_TRUE(
      vpi_compare_objects(decl, Named(vpiSequenceDecl, By("top"), "s")));
  std::vector<std::string> arguments;
  for (vpiHandle argument : ObjectsOf(vpiArgument, inst)) {
    arguments.emplace_back(vpi_get_str(vpiName, argument));
  }
  EXPECT_EQ(arguments, (std::vector<std::string>{"a", "c"}));
  EXPECT_EQ(vpi_handle(vpiExpr, inst), nullptr);
  vpiHandle whole = PropertyOf("i2");
  ASSERT_NE(whole, nullptr);
  EXPECT_EQ(vpi_get(vpiType, whole), vpiSequenceInst);
  vpiHandle whole_decl = vpi_handle(vpiSequenceDecl, whole);
  ASSERT_NE(whole_decl, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, whole_decl), "u");
}

TEST_F(SequenceExprsOfARun, AMemberOperandIsNoSequenceInst) {
  vpiHandle chain = PropertyOf("e1");
  EXPECT_EQ(OpOf(chain), vpiCycleDelayOp);
  const std::vector<vpiHandle> kParts = OperandsOf(chain);
  ASSERT_EQ(kParts.size(), 3u);
  EXPECT_NE(vpi_get(vpiType, kParts[0]), vpiSequenceInst);
}

TEST_F(SequenceExprsOfARun, ADistOperandIsADistribution) {
  vpiHandle chain = PropertyOf("x1");
  EXPECT_EQ(OpOf(chain), vpiCycleDelayOp);
  const std::vector<vpiHandle> kParts = OperandsOf(chain);
  ASSERT_FALSE(kParts.empty());
  EXPECT_EQ(vpi_get(vpiType, kParts[0]), vpiDistribution);
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiExpr, kParts[0])), "a");
  const std::vector<vpiHandle> kEntries = ObjectsOf(vpiDistItem, kParts[0]);
  ASSERT_EQ(kEntries.size(), 2u);
  EXPECT_EQ(vpi_get(vpiDistType, kEntries[1]), vpiEqualDist);
}

TEST_F(SequenceExprsOfARun, ADistOperandsDefaultItemIsADistItem) {
  const std::vector<vpiHandle> kParts = OperandsOf(PropertyOf("x2"));
  ASSERT_FALSE(kParts.empty());
  EXPECT_EQ(vpi_get(vpiType, kParts[0]), vpiDistribution);
  const std::vector<vpiHandle> kEntries = ObjectsOf(vpiDistItem, kParts[0]);
  ASSERT_EQ(kEntries.size(), 2u);
  EXPECT_EQ(vpi_get(vpiDistType, kEntries[1]), vpiDivDist);
  EXPECT_EQ(vpi_handle(vpiValueRange, kEntries[1]), nullptr);
  EXPECT_NE(vpi_handle(vpiWeight, kEntries[1]), nullptr);
}

TEST_F(SequenceExprsOfARun, RepetitionsTakeTheirBounds) {
  const struct {
    const char* name;
    int op;
    std::vector<std::string> spelled;
  } kRepeats[] = {{"r1", vpiConsecutiveRepeatOp, {"a", "2"}},
                  {"r2", vpiGotoRepeatOp, {"a", "1", "2"}},
                  {"r3", vpiRepeatOp, {"a", "3"}}};
  for (const auto& repeat : kRepeats) {
    vpiHandle chain = PropertyOf(repeat.name);
    EXPECT_EQ(OpOf(chain), vpiCycleDelayOp) << repeat.name;
    const std::vector<vpiHandle> kParts = OperandsOf(chain);
    ASSERT_FALSE(kParts.empty()) << repeat.name;
    EXPECT_EQ(OpOf(kParts[0]), repeat.op) << repeat.name;
    EXPECT_EQ(Spelled(kParts[0]), repeat.spelled) << repeat.name;
  }
}

TEST_F(SequenceExprsOfARun, JoinedAndMatchedSequences) {
  vpiHandle joined = PropertyOf("j1");
  EXPECT_EQ(OpOf(joined), vpiIntersectOp);
  const std::vector<vpiHandle> kSides = OperandsOf(joined);
  ASSERT_EQ(kSides.size(), 2u);
  EXPECT_EQ(OpOf(kSides[0]), vpiCycleDelayOp);
  EXPECT_EQ(OpOf(kSides[1]), vpiCycleDelayOp);
  vpiHandle matched = PropertyOf("m1");
  EXPECT_EQ(OpOf(matched), vpiFirstMatchOp);
  const std::vector<vpiHandle> kMatched = OperandsOf(matched);
  ASSERT_EQ(kMatched.size(), 1u);
  EXPECT_EQ(OpOf(kMatched[0]), vpiCycleDelayOp);
}

TEST_F(SequenceExprsOfARun, AnAntecedentIsItsSequenceExpr) {
  vpiHandle implication = PropertyOf("p1");
  EXPECT_EQ(OpOf(implication), vpiOverlapImplyOp);
  const std::vector<vpiHandle> kSides = OperandsOf(implication);
  ASSERT_EQ(kSides.size(), 2u);
  EXPECT_EQ(OpOf(kSides[0]), vpiCycleDelayOp);
  EXPECT_EQ(Spelled(kSides[0]), (std::vector<std::string>{"a", "b", "1"}));
  EXPECT_STREQ(vpi_get_str(vpiName, kSides[1]), "c");
}

TEST_F(SequenceExprsOfARun, ThroughoutAndWithinAreTheirOperators) {
  vpiHandle throughout = PropertyOf("t1");
  EXPECT_EQ(OpOf(throughout), vpiThroughoutOp);
  EXPECT_EQ(Spelled(throughout), (std::vector<std::string>{"a", "op"}));
  const std::vector<vpiHandle> kHeld = OperandsOf(throughout);
  ASSERT_EQ(kHeld.size(), 2u);
  EXPECT_EQ(Spelled(kHeld[1]), (std::vector<std::string>{"b", "c", "1"}));
  vpiHandle within = PropertyOf("w1");
  EXPECT_EQ(OpOf(within), vpiWithinOp);
  const std::vector<vpiHandle> kSides = OperandsOf(within);
  ASSERT_EQ(kSides.size(), 2u);
  EXPECT_EQ(Spelled(kSides[0]), (std::vector<std::string>{"a", "b", "1"}));
  EXPECT_EQ(Spelled(kSides[1]), (std::vector<std::string>{"c", "d", "3"}));
}

TEST_F(SequenceExprsOfARun, AnOperandReachesItsMatchItems) {
  vpiHandle decl = Named(vpiPropertyDecl, By("top"), "q");
  ASSERT_NE(decl, nullptr);
  vpiHandle spec = vpi_handle(vpiPropertySpec, decl);
  ASSERT_NE(spec, nullptr);
  vpiHandle chain = vpi_handle(vpiPropertyExpr, spec);
  EXPECT_EQ(OpOf(chain), vpiCycleDelayOp);
  const std::vector<vpiHandle> kParts = OperandsOf(chain);
  ASSERT_FALSE(kParts.empty());
  EXPECT_STREQ(vpi_get_str(vpiName, kParts[0]), "a");
  std::vector<vpiHandle> items;
  vpiHandle it = vpi_iterate(vpiMatchItem, kParts[0]);
  ASSERT_NE(it, nullptr);
  for (vpiHandle h = vpi_scan(it); h != nullptr; h = vpi_scan(it)) {
    items.push_back(h);
  }
  ASSERT_EQ(items.size(), 2u);
  EXPECT_EQ(vpi_get(vpiType, items[0]), vpiAssignment);
  EXPECT_EQ(vpi_get(vpiOpType, items[0]), vpiAssignmentOp);
  EXPECT_EQ(vpi_get(vpiOpType, items[1]), vpiAddOp);
  vpiHandle target = vpi_handle(vpiLhs, items[0]);
  ASSERT_NE(target, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, target), "n");
}

TEST_F(SequenceExprsOfARun, AMatchItemWritingAPartSelectHasItAsItsLhs) {
  vpiHandle decl = Named(vpiPropertyDecl, By("top"), "q2");
  ASSERT_NE(decl, nullptr);
  vpiHandle chain =
      vpi_handle(vpiPropertyExpr, vpi_handle(vpiPropertySpec, decl));
  const std::vector<vpiHandle> kParts = OperandsOf(chain);
  ASSERT_FALSE(kParts.empty());
  const std::vector<vpiHandle> kItems = ObjectsOf(vpiMatchItem, kParts[0]);
  ASSERT_EQ(kItems.size(), 1u);
  vpiHandle target = vpi_handle(vpiLhs, kItems[0]);
  ASSERT_NE(target, nullptr);
  EXPECT_EQ(vpi_get(vpiType, target), vpiPartSelect);
  vpiHandle local = vpi_handle(vpiParent, target);
  ASSERT_NE(local, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, local), "top.q2.v");
}

}  // namespace
}  // namespace delta
