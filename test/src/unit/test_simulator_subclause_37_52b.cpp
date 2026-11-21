#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class PropertySpecsEverywhere : public VpiDesignRun {
 protected:
  static std::string NameOf(vpiHandle obj) {
    const char* name = obj == nullptr ? nullptr : vpi_get_str(vpiName, obj);
    return name == nullptr ? "" : name;
  }

  static std::vector<std::string> OperandNames(vpiHandle op) {
    std::vector<std::string> names;
    for (vpiHandle operand : OperandsOf(op)) names.push_back(NameOf(operand));
    return names;
  }

  static std::vector<int> OperandValues(vpiHandle op) {
    std::vector<int> values;
    const std::vector<vpiHandle> kOperands = OperandsOf(op);
    for (size_t i = 1; i < kOperands.size(); ++i) {
      values.push_back(IntegerOf(kOperands[i]));
    }
    return values;
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

  static vpiHandle SpecNamed(const std::string& name) {
    vpiHandle it = vpi_iterate(vpiAssertion, nullptr);
    if (it == nullptr) return nullptr;
    vpiHandle spec = nullptr;
    for (vpiHandle h = vpi_scan(it); h != nullptr; h = vpi_scan(it)) {
      if (spec == nullptr && NameOf(h) == name) {
        spec = vpi_handle(vpiProperty, h);
      }
    }
    return spec;
  }

  static void ExpectSpecParts(const std::string& name) {
    vpiHandle spec = SpecNamed(name);
    ASSERT_NE(spec, nullptr) << name;
    vpiHandle event = vpi_handle(vpiClockingEvent, spec);
    ASSERT_NE(event, nullptr) << name;
    EXPECT_EQ(vpi_get(vpiOpType, event), vpiPosedgeOp) << name;
    EXPECT_EQ(OperandNames(event), (std::vector<std::string>{"clk"})) << name;
    EXPECT_EQ(NameOf(vpi_handle(vpiDisableCondition, spec)), "r") << name;
    vpiHandle body = vpi_handle(vpiPropertyExpr, spec);
    EXPECT_EQ(OpOf(body), vpiOverlapImplyOp) << name;
    EXPECT_EQ(OperandNames(body), (std::vector<std::string>{"a", "b"})) << name;
  }

  static void ExpectClockedOperand(const char* name, int op, size_t place,
                                   const char* clock) {
    vpiHandle outer = PropertyOf(name);
    EXPECT_EQ(OpOf(outer), op) << name;
    const std::vector<vpiHandle> kOperands = OperandsOf(outer);
    ASSERT_EQ(kOperands.size(), place + 1) << name;
    vpiHandle clocked = kOperands[place];
    EXPECT_EQ(vpi_get(vpiType, clocked), vpiClockedProp) << name;
    vpiHandle event = vpi_handle(vpiClockingEvent, clocked);
    ASSERT_NE(event, nullptr) << name;
    EXPECT_EQ(OperandNames(event), (std::vector<std::string>{clock})) << name;
    EXPECT_EQ(NameOf(vpi_handle(vpiPropertyExpr, clocked)), "b") << name;
  }

  static std::vector<int> ExprValues(vpiHandle item) {
    std::vector<int> values;
    for (vpiHandle expr : Reached(vpiExpr, item)) {
      values.push_back(IntegerOf(expr));
    }
    return values;
  }
};

constexpr const char* kStrongAndWeakForms =
    "module top; logic clk, a, b, c;\n"
    "  n1: assert property (@(posedge clk) nexttime [1] a);\n"
    "  n2: assert property (@(posedge clk) s_nexttime [2] a);\n"
    "  n3: assert property (@(posedge clk) s_nexttime a);\n"
    "  n4: assert property (@(posedge clk) nexttime [2] a);\n"
    "  n5: assert property (@(posedge clk) nexttime a);\n"
    "  w1: assert property (@(posedge clk) always [1:3] a);\n"
    "  w2: assert property (@(posedge clk) s_always [1:3] a);\n"
    "  w3: assert property (@(posedge clk) always [2:$] a);\n"
    "  e1: assert property (@(posedge clk) s_eventually [1:2] a);\n"
    "  e2: assert property (@(posedge clk) eventually [1:2] a);\n"
    "  e3: assert property (@(posedge clk) s_eventually a);\n"
    "  r1: assert property (@(posedge clk) reject_on (c) a);\n"
    "  r2: assert property (@(posedge clk) sync_accept_on (c) a);\n"
    "  r3: assert property (@(posedge clk) sync_reject_on (c) a);\n"
    "  r4: assert property (@(posedge clk) accept_on (c) a);\n"
    "  u1: assert property (@(posedge clk) a until b);\n"
    "  u2: assert property (@(posedge clk) a s_until b);\n"
    "  u3: assert property (@(posedge clk) a until_with b);\n"
    "  u4: assert property (@(posedge clk) a s_until_with b);\n"
    "  i1: assert property (@(posedge clk) a |-> b);\n"
    "  i2: assert property (@(posedge clk) not a);\n"
    "  q1: assert property (@(posedge clk) weak(a ##1 b));\n"
    "  q2: cover property (@(posedge clk) weak(a ##1 b));\n"
    "  q3: assume property (@(posedge clk) a ##1 b);\n"
    "  q4: restrict property (@(posedge clk) a ##1 b);\n"
    "endmodule\n";

class StrongAndWeakFormsOfARun : public PropertySpecsEverywhere {
 protected:
  void SetUp() override {
    PropertySpecsEverywhere::SetUp();
    Run(kStrongAndWeakForms);
  }
};

TEST_F(StrongAndWeakFormsOfARun, ANexttimeCountOfOneIsNoOperand) {
  vpiHandle once = PropertyOf("n1");
  EXPECT_EQ(OpOf(once), vpiNexttimeOp);
  EXPECT_EQ(OperandNames(once), (std::vector<std::string>{"a"}));
}

TEST_F(StrongAndWeakFormsOfARun, AStrongNexttimeTakesThePropertyThenItsCount) {
  vpiHandle counted = PropertyOf("n2");
  EXPECT_EQ(OpOf(counted), vpiNexttimeOp);
  EXPECT_EQ(vpi_get(vpiOpStrong, counted), 1);
  const std::vector<vpiHandle> kOperands = OperandsOf(counted);
  ASSERT_EQ(kOperands.size(), 2u);
  EXPECT_EQ(NameOf(kOperands[0]), "a");
  EXPECT_EQ(vpi_get(vpiType, kOperands[1]), vpiConstant);
  EXPECT_EQ(IntegerOf(kOperands[1]), 2);
  vpiHandle bare = PropertyOf("n3");
  EXPECT_EQ(OpOf(bare), vpiNexttimeOp);
  EXPECT_EQ(vpi_get(vpiOpStrong, bare), 1);
  EXPECT_EQ(OperandNames(bare), (std::vector<std::string>{"a"}));
}

TEST_F(StrongAndWeakFormsOfARun, AWeakNexttimeIsWeakAndKeepsItsCount) {
  EXPECT_EQ(OperandValues(PropertyOf("n4")), (std::vector<int>{2}));
  EXPECT_EQ(vpi_get(vpiOpStrong, PropertyOf("n4")), 0);
  EXPECT_EQ(vpi_get(vpiOpStrong, PropertyOf("n5")), 0);
}

TEST_F(StrongAndWeakFormsOfARun, AlwaysAndEventuallyTakeThePropertyThenBounds) {
  const struct {
    const char* name;
    int op;
    int strong;
    std::vector<int> bounds;
  } kRanged[] = {{"w1", vpiAlwaysOp, 0, {1, 3}},
                 {"w2", vpiAlwaysOp, 1, {1, 3}},
                 {"e1", vpiEventuallyOp, 1, {1, 2}},
                 {"e2", vpiEventuallyOp, 0, {1, 2}}};
  for (const auto& ranged : kRanged) {
    vpiHandle op = PropertyOf(ranged.name);
    EXPECT_EQ(OpOf(op), ranged.op) << ranged.name;
    EXPECT_EQ(vpi_get(vpiOpStrong, op), ranged.strong) << ranged.name;
    const std::vector<vpiHandle> kOperands = OperandsOf(op);
    ASSERT_EQ(kOperands.size(), 3u) << ranged.name;
    EXPECT_EQ(NameOf(kOperands[0]), "a") << ranged.name;
    EXPECT_EQ(OperandValues(op), ranged.bounds) << ranged.name;
  }
  const std::vector<vpiHandle> kOpen = OperandsOf(PropertyOf("w3"));
  ASSERT_EQ(kOpen.size(), 3u);
  EXPECT_EQ(IntegerOf(kOpen[1]), 2);
}

TEST_F(StrongAndWeakFormsOfARun, ABareStrongEventuallyTakesOnlyTheProperty) {
  vpiHandle bare = PropertyOf("e3");
  EXPECT_EQ(OpOf(bare), vpiEventuallyOp);
  EXPECT_EQ(vpi_get(vpiOpStrong, bare), 1);
  EXPECT_EQ(OperandNames(bare), (std::vector<std::string>{"a"}));
}

TEST_F(StrongAndWeakFormsOfARun, AbortsTakeTheConditionThenTheProperty) {
  const struct {
    const char* name;
    int op;
  } kAborts[] = {{"r1", vpiRejectOnOp},
                 {"r2", vpiSyncAcceptOnOp},
                 {"r3", vpiSyncRejectOnOp}};
  for (const auto& abort : kAborts) {
    vpiHandle op = PropertyOf(abort.name);
    EXPECT_EQ(OpOf(op), abort.op) << abort.name;
    EXPECT_EQ(OperandNames(op), (std::vector<std::string>{"c", "a"}))
        << abort.name;
  }
}

TEST_F(StrongAndWeakFormsOfARun, UntilsTakeTheLeftThenTheRight) {
  const struct {
    const char* name;
    int op;
    int strong;
  } kUntils[] = {{"u1", vpiUntilOp, 0},
                 {"u2", vpiUntilOp, 1},
                 {"u3", vpiUntilWithOp, 0},
                 {"u4", vpiUntilWithOp, 1}};
  for (const auto& until : kUntils) {
    vpiHandle op = PropertyOf(until.name);
    EXPECT_EQ(OpOf(op), until.op) << until.name;
    EXPECT_EQ(vpi_get(vpiOpStrong, op), until.strong) << until.name;
    EXPECT_EQ(OperandNames(op), (std::vector<std::string>{"a", "b"}))
        << until.name;
  }
}

TEST_F(StrongAndWeakFormsOfARun, AWeakOrUnstatedSequenceIsWeak) {
  for (const char* name : {"q1", "q2", "q3", "q4"}) {
    vpiHandle sequence = PropertyOf(name);
    EXPECT_EQ(OpOf(sequence), vpiCycleDelayOp) << name;
    EXPECT_EQ(vpi_get(vpiOpStrong, sequence), 0) << name;
  }
}

TEST_F(StrongAndWeakFormsOfARun,
       DISABLED_AnOperatorWithoutAStrongFormHasNoStrength) {
  for (const char* name : {"i1", "i2", "r4"}) {
    vpiHandle op = PropertyOf(name);
    ASSERT_NE(OpOf(op), 0) << name;
    EXPECT_EQ(vpi_get(vpiOpStrong, op), vpiUndefined) << name;
  }
}

TEST_F(PropertySpecsEverywhere, ASpecWithoutADisableHasNoCondition) {
  Run("module top; logic clk, a, b;\n"
      "  k1: assert property (@(posedge clk) a |-> b);\n"
      "endmodule\n");
  vpiHandle spec = SpecNamed("k1");
  ASSERT_NE(spec, nullptr);
  EXPECT_EQ(vpi_handle(vpiDisableCondition, spec), nullptr);
}

TEST_F(PropertySpecsEverywhere, ADefaultDisableIsTheSpecsCondition) {
  Run("module top; logic clk, r, a, b;\n"
      "  default disable iff r;\n"
      "  k1: assert property (@(posedge clk) a |-> b);\n"
      "endmodule\n");
  ExpectSpecParts("k1");
}

TEST_F(PropertySpecsEverywhere, EveryDirectiveAndPlaceReachesItsSpecParts) {
  Run("interface ifc(input logic clk); logic r, a, b;\n"
      "  i1: assert property (@(posedge clk) disable iff (r) a |-> b);\n"
      "endinterface\n"
      "program prg(input logic clk, r, a, b);\n"
      "  g1: assert property (@(posedge clk) disable iff (r) a |-> b);\n"
      "endprogram\n"
      "checker chk(logic clk, r, a, b);\n"
      "  h1: assert property (@(posedge clk) disable iff (r) a |-> b);\n"
      "endchecker\n"
      "module top; logic clk, r, a, b;\n"
      "  ifc i0(clk);\n"
      "  prg p0(clk, r, a, b);\n"
      "  chk k0(clk, r, a, b);\n"
      "  m1: assume property (@(posedge clk) disable iff (r) a |-> b);\n"
      "  c1: cover property (@(posedge clk) disable iff (r) a |-> b);\n"
      "  always @(a) begin\n"
      "    v1: assert property (@(posedge clk) disable iff (r) a |-> b);\n"
      "  end\n"
      "endmodule\n");
  for (const char* name : {"i1", "g1", "h1", "m1", "c1", "v1"}) {
    ExpectSpecParts(name);
  }
}

TEST_F(PropertySpecsEverywhere, AClockedPropertyStandsAsAnAndOrOperand) {
  Run("module top; logic clk1, a, b;\n"
      "  j1: assert property (@(posedge clk1) a and (@(posedge clk1) b));\n"
      "  j2: assert property (@(posedge clk1) a or (@(posedge clk1) b));\n"
      "endmodule\n");
  ExpectClockedOperand("j1", vpiCompAndOp, 1, "clk1");
  ExpectClockedOperand("j2", vpiCompOrOp, 1, "clk1");
}

TEST_F(PropertySpecsEverywhere, DISABLED_AClockedPropertyStandsAsANotOperand) {
  Run("module top; logic clk1, clk2, b;\n"
      "  n1: assert property (@(posedge clk1) not (@(posedge clk2) b));\n"
      "endmodule\n");
  ExpectClockedOperand("n1", vpiNotOp, 0, "clk2");
}

TEST_F(PropertySpecsEverywhere,
       DISABLED_ASpecReachesAParenthesizedSequenceAnd) {
  Run("module top; logic clk, a, b;\n"
      "  k1: assert property (@(posedge clk) (a and b));\n"
      "endmodule\n");
  vpiHandle body = PropertyOf("k1");
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(vpi_get(vpiType, body), vpiOperation);
  EXPECT_EQ(OperandNames(body), (std::vector<std::string>{"a", "b"}));
}

TEST_F(PropertySpecsEverywhere, ADeclarationsBodyHoldsAClockedProperty) {
  Run("module top; logic clk1, clk2, a, b;\n"
      "  property p; @(posedge clk1) a |=> @(posedge clk2) b; endproperty\n"
      "endmodule\n");
  vpiHandle decl = Named(vpiPropertyDecl, By("top"), "p");
  ASSERT_NE(decl, nullptr);
  vpiHandle body =
      vpi_handle(vpiPropertyExpr, vpi_handle(vpiPropertySpec, decl));
  EXPECT_EQ(OpOf(body), vpiNonOverlapImplyOp);
  const std::vector<vpiHandle> kSides = OperandsOf(body);
  ASSERT_EQ(kSides.size(), 2u);
  EXPECT_EQ(vpi_get(vpiType, kSides[1]), vpiClockedProp);
  EXPECT_EQ(NameOf(vpi_handle(vpiPropertyExpr, kSides[1])), "b");
}

TEST_F(PropertySpecsEverywhere, ADeclarationsWholeBodyMayBeAPropertyInst) {
  Run("module top; logic clk, a;\n"
      "  property p1(x); @(posedge clk) x; endproperty\n"
      "  property q; p1(a); endproperty\n"
      "endmodule\n");
  vpiHandle decl = Named(vpiPropertyDecl, By("top"), "q");
  ASSERT_NE(decl, nullptr);
  vpiHandle body =
      vpi_handle(vpiPropertyExpr, vpi_handle(vpiPropertySpec, decl));
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(vpi_get(vpiType, body), vpiPropertyInst);
  EXPECT_EQ(NameOf(vpi_handle(vpiPropertyDecl, body)), "p1");
}

constexpr const char* kCaseProperties =
    "module top; logic clk, a, b, c, d, e; logic [1:0] sel;\n"
    "  s1: assert property (@(posedge clk)\n"
    "        case (sel) 2, 0: a; default: b; endcase);\n"
    "  s2: assert property (@(posedge clk)\n"
    "        case (sel) 0: a; 1: b; 2, 3: c; endcase);\n"
    "  s3: assert property (@(posedge clk)\n"
    "        case (sel) 0: a |-> b; default: c; endcase);\n"
    "  s4: assert property (@(posedge clk)\n"
    "        case (sel) d, e: a; default: b; endcase);\n"
    "  s5: assert property (@(posedge clk)\n"
    "        case (sel) 0: a; 1: a; endcase);\n"
    "  property p; @(posedge clk) case (sel) 0: a; default: b; endcase\n"
    "  endproperty\n"
    "endmodule\n";

class CasePropertiesOfARun : public PropertySpecsEverywhere {
 protected:
  void SetUp() override {
    PropertySpecsEverywhere::SetUp();
    Run(kCaseProperties);
  }
};

TEST_F(CasePropertiesOfARun, AnItemsConditionsComeInTheirWrittenOrder) {
  const std::vector<vpiHandle> kItems =
      Reached(vpiCasePropertyItem, PropertyOf("s1"));
  ASSERT_EQ(kItems.size(), 2u);
  EXPECT_EQ(ExprValues(kItems[0]), (std::vector<int>{2, 0}));
}

TEST_F(CasePropertiesOfARun, EveryWrittenItemIsReachedInOrder) {
  const std::vector<vpiHandle> kItems =
      Reached(vpiCasePropertyItem, PropertyOf("s2"));
  ASSERT_EQ(kItems.size(), 3u);
  const std::vector<std::vector<int>> kConditions{{0}, {1}, {2, 3}};
  const std::vector<std::string> kProperties{"a", "b", "c"};
  for (size_t i = 0; i < kItems.size(); ++i) {
    EXPECT_EQ(ExprValues(kItems[i]), kConditions[i]) << i;
    EXPECT_EQ(NameOf(vpi_handle(vpiPropertyExpr, kItems[i])), kProperties[i])
        << i;
  }
}

TEST_F(CasePropertiesOfARun, AnItemsOperationIsItsPropertyNotACondition) {
  const std::vector<vpiHandle> kItems =
      Reached(vpiCasePropertyItem, PropertyOf("s3"));
  ASSERT_EQ(kItems.size(), 2u);
  EXPECT_EQ(ExprValues(kItems[0]), (std::vector<int>{0}));
  vpiHandle property = vpi_handle(vpiPropertyExpr, kItems[0]);
  EXPECT_EQ(OpOf(property), vpiOverlapImplyOp);
  EXPECT_EQ(OperandNames(property), (std::vector<std::string>{"a", "b"}));
}

TEST_F(CasePropertiesOfARun, VariableConditionsAreNotTakenForTheProperty) {
  const std::vector<vpiHandle> kItems =
      Reached(vpiCasePropertyItem, PropertyOf("s4"));
  ASSERT_EQ(kItems.size(), 2u);
  std::vector<std::string> conditions;
  for (vpiHandle expr : Reached(vpiExpr, kItems[0])) {
    conditions.push_back(NameOf(expr));
  }
  EXPECT_EQ(conditions, (std::vector<std::string>{"d", "e"}));
  EXPECT_EQ(NameOf(vpi_handle(vpiPropertyExpr, kItems[0])), "a");
}

TEST_F(CasePropertiesOfARun, ItemsWrittenApartStayApart) {
  const std::vector<vpiHandle> kItems =
      Reached(vpiCasePropertyItem, PropertyOf("s5"));
  ASSERT_EQ(kItems.size(), 2u);
  EXPECT_EQ(ExprValues(kItems[0]), (std::vector<int>{0}));
  EXPECT_EQ(ExprValues(kItems[1]), (std::vector<int>{1}));
}

TEST_F(CasePropertiesOfARun, ADeclarationsBodyMayBeACaseProperty) {
  vpiHandle decl = Named(vpiPropertyDecl, By("top"), "p");
  ASSERT_NE(decl, nullptr);
  vpiHandle body =
      vpi_handle(vpiPropertyExpr, vpi_handle(vpiPropertySpec, decl));
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(vpi_get(vpiType, body), vpiCaseProperty);
  EXPECT_EQ(NameOf(vpi_handle(vpiCondition, body)), "sel");
  EXPECT_EQ(Reached(vpiCasePropertyItem, body).size(), 2u);
}

TEST_F(PropertySpecsEverywhere, DISABLED_APropertysLocalVariableGivesNoValue) {
  Run("module top; logic clk, a;\n"
      "  property p; int n; @(posedge clk) (a, n = 5) |=> n == 5;\n"
      "  endproperty\n"
      "  k1: assert property (p);\n"
      "endmodule\n");
  vpiHandle n =
      Named(vpiVariables, Named(vpiPropertyDecl, By("top"), "p"), "n");
  ASSERT_NE(n, nullptr);
  s_vpi_value value{};
  value.format = vpiIntVal;
  value.value.integer = 7;
  vpi_get_value(n, &value);
  const PLI_INT32 kStatus = vpi_chk_error(nullptr);
  EXPECT_NE(kStatus, 0);
}

}  // namespace
}  // namespace delta
