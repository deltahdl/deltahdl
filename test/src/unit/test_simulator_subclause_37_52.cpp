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

TEST(PropertySpecModel, PropertyExprClassGroupsItsMemberKinds) {
  EXPECT_TRUE(VpiIsPropertyExprType(vpiOperation));
  EXPECT_TRUE(VpiIsPropertyExprType(vpiMulticlockSequenceExpr));
  EXPECT_TRUE(VpiIsPropertyExprType(vpiPropertyInst));
  EXPECT_TRUE(VpiIsPropertyExprType(vpiClockedProp));
  EXPECT_TRUE(VpiIsPropertyExprType(vpiCaseProperty));

  EXPECT_FALSE(VpiIsPropertyExprType(vpiNet));
  EXPECT_FALSE(VpiIsPropertyExprType(vpiModule));
}

TEST(PropertySpecModel, PropertyExprClassSelectorIsNotItselfAMemberKind) {
  EXPECT_FALSE(VpiIsPropertyExprType(vpiPropertyExpr));
}

TEST(PropertySpecModel, PropertyVariableValueCannotBeAccessed) {
  EXPECT_FALSE(VpiIsPropertyVariableValueAccessible());
}

TEST(PropertySpecModel, OpTypeSetCoversTheTwentyPropertyOperators) {
  for (int op : {vpiAcceptOnOp,
                 vpiAlwaysOp,
                 vpiCompAndOp,
                 vpiCompOrOp,
                 vpiEventuallyOp,
                 vpiIfElseOp,
                 vpiIfOp,
                 vpiIffOp,
                 vpiImpliesOp,
                 vpiNexttimeOp,
                 vpiNonOverlapFollowedByOp,
                 vpiNonOverlapImplyOp,
                 vpiNotOp,
                 vpiOverlapFollowedByOp,
                 vpiOverlapImplyOp,
                 vpiRejectOnOp,
                 vpiSyncAcceptOnOp,
                 vpiSyncRejectOnOp,
                 vpiUntilOp,
                 vpiUntilWithOp}) {
    EXPECT_TRUE(VpiIsPropertyExprOpType(op)) << "op=" << op;
  }
}

TEST(PropertySpecModel, OpTypeSetRejectsNonPropertyOperators) {
  EXPECT_FALSE(VpiIsPropertyExprOpType(vpiAddOp));
  EXPECT_FALSE(VpiIsPropertyExprOpType(vpiLogAndOp));
  EXPECT_FALSE(VpiIsPropertyExprOpType(vpiThroughoutOp));
  EXPECT_FALSE(VpiIsPropertyExprOpType(vpiIntersectOp));
}

TEST(PropertySpecModel, OperationReportsItsPropertyOpType) {
  VpiContext ctx;
  VpiObject op;
  op.type = vpiOperation;
  op.op_type = vpiUntilOp;

  EXPECT_EQ(ctx.Get(vpiOpType, &op), vpiUntilOp);
  EXPECT_TRUE(VpiIsPropertyExprOpType(ctx.Get(vpiOpType, &op)));
}

TEST(PropertySpecModel, NexttimeOperandOrderAndConstantOmission) {
  VpiObject prop;
  VpiObject k;

  auto with_constant = VpiNexttimeOperands(&prop, &k, true);
  ASSERT_EQ(with_constant.size(), 2u);
  EXPECT_EQ(with_constant[0], &prop);
  EXPECT_EQ(with_constant[1], &k);

  auto unit_constant = VpiNexttimeOperands(&prop, &k, false);
  ASSERT_EQ(unit_constant.size(), 1u);
  EXPECT_EQ(unit_constant[0], &prop);

  auto no_constant = VpiNexttimeOperands(&prop, nullptr, true);
  ASSERT_EQ(no_constant.size(), 1u);
  EXPECT_EQ(no_constant[0], &prop);
}

TEST(PropertySpecModel, AlwaysEventuallyOperandOrderAndRangeOmission) {
  VpiObject prop;
  VpiObject lo;
  VpiObject hi;

  auto ranged = VpiAlwaysEventuallyOperands(&prop, &lo, &hi);
  ASSERT_EQ(ranged.size(), 3u);
  EXPECT_EQ(ranged[0], &prop);
  EXPECT_EQ(ranged[1], &lo);
  EXPECT_EQ(ranged[2], &hi);

  auto unranged = VpiAlwaysEventuallyOperands(&prop, nullptr, nullptr);
  ASSERT_EQ(unranged.size(), 1u);
  EXPECT_EQ(unranged[0], &prop);

  auto left_only = VpiAlwaysEventuallyOperands(&prop, &lo, nullptr);
  ASSERT_EQ(left_only.size(), 2u);
  EXPECT_EQ(left_only[0], &prop);
  EXPECT_EQ(left_only[1], &lo);

  auto right_only = VpiAlwaysEventuallyOperands(&prop, nullptr, &hi);
  ASSERT_EQ(right_only.size(), 2u);
  EXPECT_EQ(right_only[0], &prop);
  EXPECT_EQ(right_only[1], &hi);
}

TEST(PropertySpecModel, OpStrongIsValidOnlyForTheStrongCapableOperators) {
  for (int op : {vpiNexttimeOp, vpiAlwaysOp, vpiEventuallyOp, vpiUntilOp,
                 vpiUntilWithOp}) {
    EXPECT_TRUE(VpiIsOpStrongValidOp(op)) << "op=" << op;
  }

  EXPECT_FALSE(VpiIsOpStrongValidOp(vpiImpliesOp));
  EXPECT_FALSE(VpiIsOpStrongValidOp(vpiNotOp));
  EXPECT_FALSE(VpiIsOpStrongValidOp(vpiAcceptOnOp));
}

TEST(PropertySpecModel, OperationReportsOpStrongProperty) {
  VpiContext ctx;
  VpiObject strong;
  strong.type = vpiOperation;
  strong.op_type = vpiUntilOp;
  strong.op_strong = true;
  EXPECT_EQ(ctx.Get(vpiOpStrong, &strong), 1);

  VpiObject weak;
  weak.type = vpiOperation;
  weak.op_type = vpiUntilOp;
  EXPECT_EQ(ctx.Get(vpiOpStrong, &weak), 0);
}

TEST(PropertySpecModel, CaseItemGroupsConditionsBranchingToOneStatement) {
  VpiContext ctx;
  VpiObject item;
  item.type = vpiCasePropertyItem;
  VpiObject c0;
  c0.type = vpiExpr;
  VpiObject c1;
  c1.type = vpiExpr;
  VpiObject branch;
  branch.type = vpiExpr;
  item.children = {&c0, &c1};
  item.body = &branch;

  auto conditions = VpiCaseItemConditions(&item);
  ASSERT_EQ(conditions.size(), 2u);
  EXPECT_EQ(conditions[0], &c0);
  EXPECT_EQ(conditions[1], &c1);

  EXPECT_EQ(ctx.Handle(vpiPropertyExpr, &item), &branch);
}

TEST(PropertySpecModel, DefaultCaseItemHasNoConditionsAndIteratesToNull) {
  VpiContext ctx;
  VpiObject default_item;
  default_item.type = vpiCasePropertyItem;

  EXPECT_TRUE(VpiCaseItemConditions(&default_item).empty());
  EXPECT_EQ(ctx.Iterate(vpiExpr, &default_item), nullptr);

  VpiObject item;
  item.type = vpiCasePropertyItem;
  VpiObject c0;
  c0.type = vpiExpr;
  item.children = {&c0};
  VpiHandle it = ctx.Iterate(vpiExpr, &item);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(ctx.Scan(it), &c0);
  EXPECT_EQ(ctx.Scan(it), nullptr);
}

TEST(PropertySpecModel, CasePropertySelectsOnItsConditionExpression) {
  VpiContext ctx;
  VpiObject case_prop;
  case_prop.type = vpiCaseProperty;
  VpiObject sel;
  sel.type = vpiExpr;
  VpiObject item;
  item.type = vpiCasePropertyItem;
  case_prop.children = {&sel, &item};

  EXPECT_EQ(VpiCasePropertyConditionExpr(&case_prop), &sel);
  EXPECT_EQ(ctx.Handle(vpiCondition, &case_prop), &sel);

  VpiObject no_condition;
  no_condition.type = vpiCaseProperty;
  VpiObject only_item;
  only_item.type = vpiCasePropertyItem;
  no_condition.children = {&only_item};
  EXPECT_EQ(VpiCasePropertyConditionExpr(&no_condition), nullptr);
  EXPECT_EQ(ctx.Handle(vpiCondition, &no_condition), nullptr);
  EXPECT_EQ(VpiCasePropertyConditionExpr(nullptr), nullptr);
}

TEST(PropertySpecModel, ClockingEventRelationIsSharedBySpecAndClockedProperty) {
  VpiObject spec;
  spec.type = vpiPropertySpec;
  VpiObject ev;
  ev.type = vpiEventControl;
  spec.children = {&ev};
  EXPECT_EQ(VpiClockingEvent(&spec), &ev);

  VpiObject clocked;
  clocked.type = vpiClockedProp;
  VpiObject ev2;
  ev2.type = vpiEventControl;
  clocked.children = {&ev2};
  EXPECT_EQ(VpiClockingEvent(&clocked), &ev2);

  VpiObject unclocked;
  unclocked.type = vpiPropertySpec;
  EXPECT_EQ(VpiClockingEvent(&unclocked), nullptr);
  EXPECT_EQ(VpiClockingEvent(nullptr), nullptr);
}

TEST(PropertySpecModel, ARecordedClockIsTheClockingEvent) {
  VpiObject spec;
  spec.type = vpiPropertySpec;
  VpiObject clock;
  clock.type = vpiOperation;
  VpiObject control;
  control.type = vpiEventControl;
  spec.children = {&control};
  spec.clocking_event = &clock;
  EXPECT_EQ(VpiClockingEvent(&spec), &clock);
}

TEST(PropertySpecModel, PropertySpecReachesItsPropertyExpr) {
  VpiObject spec;
  spec.type = vpiPropertySpec;
  VpiObject pe;
  pe.type = vpiOperation;
  spec.children = {&pe};
  EXPECT_EQ(VpiPropertyExprChild(&spec), &pe);

  VpiObject empty;
  empty.type = vpiPropertySpec;
  EXPECT_EQ(VpiPropertyExprChild(&empty), nullptr);
}

TEST(PropertySpecModel, ClockedPropertyReachesItsPropertyExpr) {
  VpiObject clocked;
  clocked.type = vpiClockedProp;
  VpiObject pe;
  pe.type = vpiOperation;
  clocked.children = {&pe};
  EXPECT_EQ(VpiPropertyExprChild(&clocked), &pe);

  VpiObject empty;
  empty.type = vpiClockedProp;
  EXPECT_EQ(VpiPropertyExprChild(&empty), nullptr);
}

TEST(PropertySpecModel, CasePropertyIteratesToItsCasePropertyItems) {
  VpiContext ctx;
  VpiObject case_prop;
  case_prop.type = vpiCaseProperty;
  VpiObject sel;
  sel.type = vpiExpr;
  VpiObject item0;
  item0.type = vpiCasePropertyItem;
  VpiObject item1;
  item1.type = vpiCasePropertyItem;
  case_prop.children = {&sel, &item0, &item1};

  VpiHandle it = ctx.Iterate(vpiCasePropertyItem, &case_prop);
  ASSERT_NE(it, nullptr);
  std::vector<VpiHandle> seen;
  while (VpiHandle h = ctx.Scan(it)) seen.push_back(h);
  ASSERT_EQ(seen.size(), 2u);
  EXPECT_EQ(seen[0], &item0);
  EXPECT_EQ(seen[1], &item1);
}

TEST(PropertySpecModel, DisableConditionReachesExpressionOrDistribution) {
  EXPECT_TRUE(VpiIsDisableConditionType(vpiExpr));
  EXPECT_TRUE(VpiIsDisableConditionType(vpiDistribution));
  EXPECT_TRUE(VpiIsDisableConditionType(vpiOperation));

  EXPECT_FALSE(VpiIsDisableConditionType(vpiModule));
  EXPECT_FALSE(VpiIsDisableConditionType(vpiNet));
}

constexpr const char* kPropertyOperators =
    "module top; logic clk, a, b, c;\n"
    "  i1: assert property (@(posedge clk) a |-> b);\n"
    "  i2: assert property (@(posedge clk) a |=> b);\n"
    "  f1: assert property (@(posedge clk) a #-# b);\n"
    "  f2: assert property (@(posedge clk) a #=# b);\n"
    "  n1: assert property (@(posedge clk) not (a s_until_with b));\n"
    "  u1: assert property (@(posedge clk) a until b);\n"
    "  x1: assert property (@(posedge clk) nexttime [2] a);\n"
    "  x2: assert property (@(posedge clk) nexttime a);\n"
    "  w1: assert property (@(posedge clk) always [1:3] a);\n"
    "  e1: assert property (@(posedge clk) s_eventually [1:2] a);\n"
    "  r1: assert property (@(posedge clk) accept_on (b) a);\n"
    "  r2: assert property (@(posedge clk) sync_reject_on (b) a);\n"
    "  c1: assert property (@(posedge clk) if (a) b else c);\n"
    "  c2: assert property (@(posedge clk) if (a) b);\n"
    "  j1: assert property (@(posedge clk) (a |-> b) and (a |-> c));\n"
    "  j2: assert property (@(posedge clk) (a |-> b) or (a |-> c));\n"
    "  j3: assert property (@(posedge clk) (a |-> b) implies (a |-> c));\n"
    "  j4: assert property (@(posedge clk) (a |-> b) iff (a |-> c));\n"
    "  w2: assert property (@(posedge clk) always [2:$] a);\n"
    "  e2: assert property (@(posedge clk) s_eventually [2:$] a);\n"
    "  w3: assert property (@(posedge clk) always a);\n"
    "  g1: assert property (@(posedge clk) strong(a ##1 b));\n"
    "  g2: assert property (@(posedge clk) a ##1 b);\n"
    "  g3: assert property (@(posedge clk) a |-> strong(b ##1 c));\n"
    "  g4: cover property (@(posedge clk) a ##1 b);\n"
    "endmodule\n";

class PropertyExprsOfARun : public VpiDesignRun {
 protected:
  static std::vector<std::string> OperandNames(vpiHandle op) {
    std::vector<std::string> names;
    for (vpiHandle operand : OperandsOf(op)) {
      const char* name = vpi_get_str(vpiName, operand);
      names.emplace_back(name == nullptr ? "" : name);
    }
    return names;
  }
};

class PropertyOperationsOfARun : public PropertyExprsOfARun {
 protected:
  void SetUp() override {
    PropertyExprsOfARun::SetUp();
    Run(kPropertyOperators);
  }
};

TEST_F(PropertyOperationsOfARun, ImplicationsAndFollowedBysAreTheirOperators) {
  EXPECT_EQ(OpOf(PropertyOf("i1")), vpiOverlapImplyOp);
  EXPECT_EQ(OpOf(PropertyOf("i2")), vpiNonOverlapImplyOp);
  EXPECT_EQ(OpOf(PropertyOf("f1")), vpiOverlapFollowedByOp);
  EXPECT_EQ(OpOf(PropertyOf("f2")), vpiNonOverlapFollowedByOp);
  const std::vector<std::string> kAThenB{"a", "b"};
  for (const char* name : {"i1", "i2", "f1", "f2"}) {
    EXPECT_EQ(OperandNames(PropertyOf(name)), kAThenB) << name;
  }
}

TEST_F(PropertyOperationsOfARun, UntilsReportTheirStrength) {
  vpiHandle negation = PropertyOf("n1");
  EXPECT_EQ(OpOf(negation), vpiNotOp);
  const std::vector<vpiHandle> kNegated = OperandsOf(negation);
  ASSERT_EQ(kNegated.size(), 1u);
  EXPECT_EQ(OpOf(kNegated[0]), vpiUntilWithOp);
  EXPECT_EQ(vpi_get(vpiOpStrong, kNegated[0]), 1);
  EXPECT_EQ(OperandNames(kNegated[0]), (std::vector<std::string>{"a", "b"}));
  vpiHandle weak = PropertyOf("u1");
  EXPECT_EQ(OpOf(weak), vpiUntilOp);
  EXPECT_EQ(vpi_get(vpiOpStrong, weak), 0);
}

TEST_F(PropertyOperationsOfARun, CountedOperatorsTakeTheirBounds) {
  vpiHandle counted = PropertyOf("x1");
  EXPECT_EQ(OpOf(counted), vpiNexttimeOp);
  const std::vector<vpiHandle> kCounted = OperandsOf(counted);
  ASSERT_EQ(kCounted.size(), 2u);
  EXPECT_STREQ(vpi_get_str(vpiName, kCounted[0]), "a");
  EXPECT_EQ(vpi_get(vpiType, kCounted[1]), vpiConstant);
  EXPECT_EQ(OperandsOf(PropertyOf("x2")).size(), 1u);
  vpiHandle always = PropertyOf("w1");
  EXPECT_EQ(OpOf(always), vpiAlwaysOp);
  EXPECT_EQ(OperandsOf(always).size(), 3u);
  EXPECT_EQ(vpi_get(vpiOpStrong, always), 0);
  vpiHandle eventually = PropertyOf("e1");
  EXPECT_EQ(OpOf(eventually), vpiEventuallyOp);
  EXPECT_EQ(OperandsOf(eventually).size(), 3u);
  EXPECT_EQ(vpi_get(vpiOpStrong, eventually), 1);
}

TEST_F(PropertyOperationsOfARun, ConditionsComeFirst) {
  EXPECT_EQ(OpOf(PropertyOf("r1")), vpiAcceptOnOp);
  EXPECT_EQ(OpOf(PropertyOf("r2")), vpiSyncRejectOnOp);
  EXPECT_EQ(OperandNames(PropertyOf("r1")),
            (std::vector<std::string>{"b", "a"}));
  EXPECT_EQ(OpOf(PropertyOf("c1")), vpiIfElseOp);
  EXPECT_EQ(OperandNames(PropertyOf("c1")),
            (std::vector<std::string>{"a", "b", "c"}));
  EXPECT_EQ(OpOf(PropertyOf("c2")), vpiIfOp);
  EXPECT_EQ(OperandNames(PropertyOf("c2")),
            (std::vector<std::string>{"a", "b"}));
}

TEST_F(PropertyOperationsOfARun, BinaryOperatorsJoinTwoProperties) {
  const struct {
    const char* name;
    int op;
  } kJoins[] = {{"j1", vpiCompAndOp},
                {"j2", vpiCompOrOp},
                {"j3", vpiImpliesOp},
                {"j4", vpiIffOp}};
  for (const auto& join : kJoins) {
    vpiHandle property = PropertyOf(join.name);
    EXPECT_EQ(OpOf(property), join.op) << join.name;
    const std::vector<vpiHandle> kSides = OperandsOf(property);
    ASSERT_EQ(kSides.size(), 2u) << join.name;
    EXPECT_EQ(OpOf(kSides[0]), vpiOverlapImplyOp) << join.name;
    EXPECT_EQ(OpOf(kSides[1]), vpiOverlapImplyOp) << join.name;
  }
}

TEST_F(PropertyOperationsOfARun, ARangeToDollarEndsInTheUnboundedConstant) {
  for (const char* name : {"w2", "e2"}) {
    const std::vector<vpiHandle> kOperands = OperandsOf(PropertyOf(name));
    ASSERT_EQ(kOperands.size(), 3u) << name;
    EXPECT_STREQ(vpi_get_str(vpiName, kOperands[0]), "a") << name;
    EXPECT_NE(vpi_get(vpiConstType, kOperands[1]), vpiUnboundedConst) << name;
    EXPECT_EQ(vpi_get(vpiType, kOperands[2]), vpiConstant) << name;
    EXPECT_EQ(vpi_get(vpiConstType, kOperands[2]), vpiUnboundedConst) << name;
  }
  EXPECT_EQ(OperandsOf(PropertyOf("w3")).size(), 1u);
}

TEST_F(PropertyOperationsOfARun, AStrongSequenceReportsItsStrength) {
  vpiHandle strong = PropertyOf("g1");
  EXPECT_EQ(OpOf(strong), vpiCycleDelayOp);
  EXPECT_EQ(vpi_get(vpiOpStrong, strong), 1);
  vpiHandle weak = PropertyOf("g2");
  EXPECT_EQ(OpOf(weak), vpiCycleDelayOp);
  EXPECT_EQ(vpi_get(vpiOpStrong, weak), 0);
  const std::vector<vpiHandle> kSides = OperandsOf(PropertyOf("g3"));
  ASSERT_EQ(kSides.size(), 2u);
  EXPECT_EQ(OpOf(kSides[1]), vpiCycleDelayOp);
  EXPECT_EQ(vpi_get(vpiOpStrong, kSides[1]), 1);
  vpiHandle covered = PropertyOf("g4");
  EXPECT_EQ(OpOf(covered), vpiCycleDelayOp);
  EXPECT_EQ(vpi_get(vpiOpStrong, covered), 1);
}

TEST_F(PropertyExprsOfARun, ADisableConditionWrittenAsADistIsADistribution) {
  Run("module top; logic clk, a, b; logic [1:0] x;\n"
      "  d1: assert property (@(posedge clk)\n"
      "        disable iff (x dist {0 := 1, [1:3] :/ 2}) a |-> b);\n"
      "endmodule\n");
  vpiHandle assertion = Named(vpiAssertion, By("top"), "d1");
  ASSERT_NE(assertion, nullptr);
  vpiHandle spec = vpi_handle(vpiProperty, assertion);
  ASSERT_NE(spec, nullptr);
  vpiHandle dist = vpi_handle(vpiDisableCondition, spec);
  ASSERT_NE(dist, nullptr);
  EXPECT_EQ(vpi_get(vpiType, dist), vpiDistribution);
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiExpr, dist)), "x");
  const std::vector<vpiHandle> kEntries = ObjectsOf(vpiDistItem, dist);
  ASSERT_EQ(kEntries.size(), 2u);
  EXPECT_EQ(vpi_get(vpiDistType, kEntries[0]), vpiEqualDist);
  EXPECT_EQ(vpi_get(vpiDistType, kEntries[1]), vpiDivDist);
  EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiValueRange, kEntries[0])),
            vpiConstant);
  EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiValueRange, kEntries[1])), vpiRange);
}

TEST_F(PropertyExprsOfARun, ANamedPropertyOperandIsAPropertyInst) {
  Run("module top; logic clk, a, b;\n"
      "  property p1(x); x; endproperty\n"
      "  property p2(x, y); x |-> y; endproperty\n"
      "  property p3(x); b |-> strong(x ##1 b); endproperty\n"
      "  k1: assert property (@(posedge clk) p1(a) and b);\n"
      "  k2: assert property (@(posedge clk) b |-> p2(a, b));\n"
      "  k3: assert property (@(posedge clk) p3(a) or b);\n"
      "endmodule\n");
  const auto kDeclOf = [](vpiHandle inst) -> std::string {
    vpiHandle decl = vpi_handle(vpiPropertyDecl, inst);
    return decl == nullptr ? "" : vpi_get_str(vpiName, decl);
  };
  const std::vector<vpiHandle> kJoined = OperandsOf(PropertyOf("k1"));
  ASSERT_EQ(kJoined.size(), 2u);
  EXPECT_EQ(vpi_get(vpiType, kJoined[0]), vpiPropertyInst);
  EXPECT_EQ(kDeclOf(kJoined[0]), "p1");
  EXPECT_EQ(NamesOf(vpiArgument, kJoined[0]), (std::vector<std::string>{"a"}));
  EXPECT_STREQ(vpi_get_str(vpiName, kJoined[1]), "b");
  const std::vector<vpiHandle> kImplied = OperandsOf(PropertyOf("k2"));
  ASSERT_EQ(kImplied.size(), 2u);
  EXPECT_EQ(vpi_get(vpiType, kImplied[1]), vpiPropertyInst);
  EXPECT_EQ(kDeclOf(kImplied[1]), "p2");
  EXPECT_EQ(NamesOf(vpiArgument, kImplied[1]),
            (std::vector<std::string>{"a", "b"}));
  const std::vector<vpiHandle> kEither = OperandsOf(PropertyOf("k3"));
  ASSERT_EQ(kEither.size(), 2u);
  EXPECT_EQ(vpi_get(vpiType, kEither[0]), vpiPropertyInst);
  EXPECT_EQ(kDeclOf(kEither[0]), "p3");
  EXPECT_EQ(NamesOf(vpiArgument, kEither[0]), (std::vector<std::string>{"a"}));
}

constexpr const char* kClockedAndCaseProperties =
    "module top; logic clk1, clk2, a, b; logic [1:0] sel;\n"
    "  k1: assert property (@(posedge clk1) a |=> @(posedge clk2) b);\n"
    "  s1: assert property (@(posedge clk1)\n"
    "        case (sel) 0, 1: a; default: b; endcase);\n"
    "endmodule\n";

class ClockedAndCasePropertiesOfARun : public PropertyExprsOfARun {
 protected:
  void SetUp() override {
    PropertyExprsOfARun::SetUp();
    Run(kClockedAndCaseProperties);
  }

  static std::vector<vpiHandle> Reached(int type, vpiHandle ref) {
    std::vector<vpiHandle> reached;
    vpiHandle it = ref == nullptr ? nullptr : vpi_iterate(type, ref);
    if (it == nullptr) return reached;
    for (vpiHandle h = vpi_scan(it); h != nullptr; h = vpi_scan(it)) {
      reached.push_back(h);
    }
    return reached;
  }
};

TEST_F(ClockedAndCasePropertiesOfARun, AClockedOperandIsAClockedProperty) {
  vpiHandle implication = PropertyOf("k1");
  EXPECT_EQ(OpOf(implication), vpiNonOverlapImplyOp);
  const std::vector<vpiHandle> kSides = OperandsOf(implication);
  ASSERT_EQ(kSides.size(), 2u);
  EXPECT_STREQ(vpi_get_str(vpiName, kSides[0]), "a");
  vpiHandle clocked = kSides[1];
  EXPECT_EQ(vpi_get(vpiType, clocked), vpiClockedProp);
  vpiHandle event = vpi_handle(vpiClockingEvent, clocked);
  ASSERT_NE(event, nullptr);
  EXPECT_EQ(vpi_get(vpiOpType, event), vpiPosedgeOp);
  vpiHandle clocked_property = vpi_handle(vpiPropertyExpr, clocked);
  ASSERT_NE(clocked_property, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, clocked_property), "b");
}

TEST_F(ClockedAndCasePropertiesOfARun, ACasePropertyReachesItsItems) {
  vpiHandle property = PropertyOf("s1");
  ASSERT_NE(property, nullptr);
  EXPECT_EQ(vpi_get(vpiType, property), vpiCaseProperty);
  vpiHandle condition = vpi_handle(vpiCondition, property);
  ASSERT_NE(condition, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, condition), "sel");
  const std::vector<vpiHandle> kItems = Reached(vpiCasePropertyItem, property);
  ASSERT_EQ(kItems.size(), 2u);
  EXPECT_EQ(Reached(vpiExpr, kItems[0]).size(), 2u);
  EXPECT_EQ(vpi_iterate(vpiExpr, kItems[1]), nullptr);
  vpiHandle first = vpi_handle(vpiPropertyExpr, kItems[0]);
  vpiHandle second = vpi_handle(vpiPropertyExpr, kItems[1]);
  ASSERT_NE(first, nullptr);
  ASSERT_NE(second, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, first), "a");
  EXPECT_STREQ(vpi_get_str(vpiName, second), "b");
}

TEST(PropertySpecModel, AnExprIterationOfANonItemIsNoConditionWalk) {
  VpiObject case_prop;
  case_prop.type = vpiCaseProperty;
  VpiObject selector;
  selector.type = vpiExpr;
  case_prop.children = {&selector};
  VpiObject iter;
  EXPECT_FALSE(VpiCollectNestedObjects(vpiExpr, &case_prop, &iter));
  EXPECT_TRUE(iter.children.empty());
}

TEST(PropertySpecificationModel, ConditionsAndPropertyExpressionLookups) {
  EXPECT_TRUE(VpiCaseItemConditions(nullptr).empty());

  VpiObject attribute;
  attribute.type = vpiAttribute;
  VpiObject item;
  item.type = vpiCasePropertyItem;
  VpiObject operation;
  operation.type = vpiOperation;
  VpiObject case_property;
  case_property.type = vpiCaseProperty;
  case_property.children = {&attribute, &item, &operation};
  EXPECT_EQ(VpiCasePropertyConditionExpr(&case_property), &operation);

  EXPECT_TRUE(VpiIsDisableConditionType(vpiConstant));
  EXPECT_TRUE(VpiIsDisableConditionType(vpiRefObj));

  EXPECT_EQ(VpiPropertyExprChild(nullptr), nullptr);
  VpiObject spec;
  spec.type = vpiPropertySpec;
  spec.children = {&attribute};
  EXPECT_EQ(VpiPropertyExprChild(&spec), nullptr);
}

TEST(PropertySpecModel, PropertyExprOfASpecAndTagsItDoesNotDraw) {
  VpiObject attribute;
  attribute.type = vpiAttribute;
  VpiObject seq_inst;
  seq_inst.type = vpiSequenceInst;
  VpiObject spec;
  spec.type = vpiPropertySpec;
  spec.children = {&attribute, &seq_inst};
  VpiHandle out = nullptr;
  EXPECT_TRUE(TryResolveProcessAndStmtRelation(vpiPropertyExpr, &spec, out));
  EXPECT_EQ(out, &seq_inst);

  VpiObject bare;
  bare.type = vpiPropertySpec;
  bare.children = {&attribute};
  EXPECT_TRUE(TryResolveProcessAndStmtRelation(vpiPropertyExpr, &bare, out));
  EXPECT_EQ(out, nullptr);
  EXPECT_FALSE(TryResolveProcessAndStmtRelation(vpiTypespec, &spec, out));
}

TEST_F(PropertyExprsOfARun, ADeclarationsBodyReachesItsFormalAsARefObj) {
  Run("module top; logic clk;\n"
      "  property p(x); @(posedge clk) x; endproperty\n"
      "endmodule\n");
  vpiHandle decl = Named(vpiPropertyDecl, By("top"), "p");
  ASSERT_NE(decl, nullptr);
  vpiHandle spec = vpi_handle(vpiPropertySpec, decl);
  ASSERT_NE(spec, nullptr);
  vpiHandle x = vpi_handle(vpiPropertyExpr, spec);
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(vpi_get(vpiType, x), vpiRefObj);
  EXPECT_STREQ(vpi_get_str(vpiName, x), "x");
  EXPECT_EQ(vpi_handle(vpiActual, x), nullptr);
}

TEST_F(PropertyExprsOfARun, ADeclarationsSpecWithoutItsSemicolonIsItsSpec) {
  Run("module top; logic clk;\n"
      "  property p(x); @(posedge clk) x endproperty\n"
      "endmodule\n");
  vpiHandle decl = Named(vpiPropertyDecl, By("top"), "p");
  ASSERT_NE(decl, nullptr);
  vpiHandle spec = vpi_handle(vpiPropertySpec, decl);
  ASSERT_NE(spec, nullptr);
  EXPECT_NE(vpi_handle(vpiClockingEvent, spec), nullptr);
  vpiHandle x = vpi_handle(vpiPropertyExpr, spec);
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(vpi_get(vpiType, x), vpiRefObj);
  EXPECT_STREQ(vpi_get_str(vpiName, x), "x");
}

TEST_F(PropertyExprsOfARun, AStrongSequenceOverAnOperandOfNoObjectIsNone) {
  Run("module top; logic clk, b; wire nw[2]; int i;\n"
      "  k1: assert property (@(posedge clk) strong(nw[i] ##1 b));\n"
      "  k2: assert property (@(posedge clk) strong(b ##1 b));\n"
      "endmodule\n");
  vpiHandle assertion = Named(vpiAssertion, By("top"), "k1");
  ASSERT_NE(assertion, nullptr);
  EXPECT_NE(vpi_handle(vpiProperty, assertion), nullptr);
  EXPECT_EQ(PropertyOf("k1"), nullptr);
  EXPECT_EQ(vpi_get(vpiOpStrong, PropertyOf("k2")), 1);
}

}  // namespace
}  // namespace delta
