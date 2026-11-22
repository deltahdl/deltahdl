#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class SequenceInstsEverywhere : public VpiDesignRun {
 protected:
  static std::string NameOf(vpiHandle obj) {
    const char* name = obj == nullptr ? nullptr : vpi_get_str(vpiName, obj);
    return name == nullptr ? "" : name;
  }

  static std::vector<std::string> ArgumentsOf(const char* label) {
    std::vector<std::string> names;
    vpiHandle inst = PropertyOf(label);
    if (inst == nullptr) return names;
    for (vpiHandle argument : ObjectsOf(vpiArgument, inst)) {
      const bool kOperation = vpi_get(vpiType, argument) == vpiOperation;
      names.push_back(kOperation ? "op" : NameOf(argument));
    }
    return names;
  }

  static vpiHandle FirstArgumentOf(const char* label) {
    const std::vector<vpiHandle> kArguments =
        ObjectsOf(vpiArgument, PropertyOf(label));
    return kArguments.empty() ? nullptr : kArguments.front();
  }

  static vpiHandle AssertionBody(const std::string& label) {
    vpiHandle it = vpi_iterate(vpiAssertion, nullptr);
    if (it == nullptr) return nullptr;
    vpiHandle found = nullptr;
    for (vpiHandle h = vpi_scan(it); h != nullptr; h = vpi_scan(it)) {
      if (found == nullptr && NameOf(h) == label) found = h;
    }
    return vpi_handle(vpiPropertyExpr, vpi_handle(vpiProperty, found));
  }

  static void ExpectFourKinds(vpiHandle scope, const char* prefix) {
    const struct {
      const char* suffix;
      int type;
    } kKinds[] = {{"op", vpiOperation},
                  {"inst", vpiSequenceInst},
                  {"dist", vpiDistribution},
                  {"expr", vpiLogicVar}};
    for (const auto& kind : kKinds) {
      const std::string kLabel = std::string(prefix) + kind.suffix;
      vpiHandle body =
          scope == nullptr
              ? AssertionBody(kLabel)
              : vpi_handle(vpiExpr, Named(vpiSequenceDecl, scope, kLabel));
      ASSERT_NE(body, nullptr) << kLabel;
      EXPECT_EQ(vpi_get(vpiType, body), kind.type) << kLabel;
    }
  }

  static std::vector<vpiHandle> ItemsOfFirstOperand(vpiHandle chain) {
    const std::vector<vpiHandle> kParts = OperandsOf(chain);
    if (kParts.empty()) return {};
    return ObjectsOf(vpiMatchItem, kParts.front());
  }

  static vpiHandle PropertyBody(const char* property) {
    return vpi_handle(vpiPropertyExpr,
                      vpi_handle(vpiPropertySpec,
                                 Named(vpiPropertyDecl, By("top"), property)));
  }
};

constexpr const char* kArgumentBindings =
    "module top; logic clk, a, b, c;\n"
    "  sequence s2(x, y = c); x ##1 y; endsequence\n"
    "  sequence s3(x, y = c, z); x ##1 y ##1 z; endsequence\n"
    "  sequence sf(x = c, y); x ##1 y; endsequence\n"
    "  sequence sq(x, y = a ##1 b); x ##1 y; endsequence\n"
    "  g1: assert property (@(posedge clk) s2(a, b));\n"
    "  g2: assert property (@(posedge clk) s3(a, , b));\n"
    "  g3: assert property (@(posedge clk) s2(.y(b), .x(a)));\n"
    "  g4: assert property (@(posedge clk) s2(.x(a)));\n"
    "  g5: assert property (@(posedge clk) sf(, b));\n"
    "  g6: assert property (@(posedge clk) sq(c));\n"
    "endmodule\n";

TEST_F(SequenceInstsEverywhere, AGivenActualOverridesItsFormalsDefault) {
  Run(kArgumentBindings);
  EXPECT_EQ(ArgumentsOf("g1"), (std::vector<std::string>{"a", "b"}));
}

TEST_F(SequenceInstsEverywhere, AnEmptyMiddleActualTakesItsDefault) {
  Run(kArgumentBindings);
  EXPECT_EQ(ArgumentsOf("g2"), (std::vector<std::string>{"a", "c", "b"}));
}

TEST_F(SequenceInstsEverywhere, DISABLED_NamedActualsComeBackInFormalOrder) {
  Run(kArgumentBindings);
  EXPECT_EQ(ArgumentsOf("g3"), (std::vector<std::string>{"a", "b"}));
}

TEST_F(SequenceInstsEverywhere, ANamedBindingLeavingOutAFormalTakesItsDefault) {
  Run(kArgumentBindings);
  EXPECT_EQ(ArgumentsOf("g4"), (std::vector<std::string>{"a", "c"}));
}

TEST_F(SequenceInstsEverywhere, AnEmptyLeadingActualTakesItsDefault) {
  Run(kArgumentBindings);
  EXPECT_EQ(ArgumentsOf("g5"), (std::vector<std::string>{"c", "b"}));
}

TEST_F(SequenceInstsEverywhere,
       DISABLED_ASequenceExpressionDefaultIsAnArgument) {
  Run(kArgumentBindings);
  EXPECT_EQ(ArgumentsOf("g6"), (std::vector<std::string>{"c", "op"}));
  const std::vector<vpiHandle> kArguments =
      ObjectsOf(vpiArgument, PropertyOf("g6"));
  ASSERT_EQ(kArguments.size(), 2u);
  EXPECT_EQ(OpOf(kArguments[1]), vpiCycleDelayOp);
}

TEST_F(SequenceInstsEverywhere, APackagesInstTakesArgumentsInFormalOrder) {
  Run("package pk; logic c;\n"
      "  sequence ps(x, y = c); x ##1 y; endsequence\n"
      "endpackage\n"
      "module top; import pk::*; logic clk, a, b;\n"
      "  k1: assert property (@(posedge clk) pk::ps(a));\n"
      "  k2: assert property (@(posedge clk) ps(b));\n"
      "endmodule\n");
  EXPECT_EQ(ArgumentsOf("k1"), (std::vector<std::string>{"a", "c"}));
  EXPECT_EQ(ArgumentsOf("k2"), (std::vector<std::string>{"b", "c"}));
}

constexpr const char* kArgumentKinds =
    "module top; logic clk, a, b, c; event ev;\n"
    "  sequence s(x, y); x ##1 y; endsequence\n"
    "  sequence se(e); @(e) a; endsequence\n"
    "  sequence u; a; endsequence\n"
    "  k1: assert property (@(posedge clk) s(a ##1 b, c));\n"
    "  k2: assert property (@(posedge clk) se(ev));\n"
    "  k3: assert property (@(posedge clk) s(u, c));\n"
    "  k4: assert property (@(posedge clk) s(a dist {0 := 1, 1 := 3}, c));\n"
    "endmodule\n";

TEST_F(SequenceInstsEverywhere, ASequenceExpressionArgumentIsAnOperation) {
  Run(kArgumentKinds);
  vpiHandle argument = FirstArgumentOf("k1");
  ASSERT_NE(argument, nullptr);
  EXPECT_EQ(OpOf(argument), vpiCycleDelayOp);
}

TEST_F(SequenceInstsEverywhere, ANamedEventArgumentIsTheEvent) {
  Run(kArgumentKinds);
  vpiHandle argument = FirstArgumentOf("k2");
  ASSERT_NE(argument, nullptr);
  EXPECT_EQ(vpi_get(vpiType, argument), vpiNamedEvent);
  EXPECT_EQ(NameOf(argument), "ev");
}

TEST_F(SequenceInstsEverywhere, DISABLED_ASequenceArgumentIsAnInstOfItsDecl) {
  Run(kArgumentKinds);
  vpiHandle argument = FirstArgumentOf("k3");
  ASSERT_NE(argument, nullptr);
  EXPECT_EQ(vpi_get(vpiType, argument), vpiSequenceInst);
  EXPECT_EQ(NameOf(vpi_handle(vpiSequenceDecl, argument)), "u");
}

TEST_F(SequenceInstsEverywhere, DISABLED_ADistributionArgumentIsADistribution) {
  Run(kArgumentKinds);
  vpiHandle argument = FirstArgumentOf("k4");
  ASSERT_NE(argument, nullptr);
  EXPECT_EQ(vpi_get(vpiType, argument), vpiDistribution);
}

constexpr const char* kMatchItems =
    "module top; logic clk, a, b;\n"
    "  function automatic bit f(); return 1; endfunction\n"
    "  property pt; @(posedge clk) (a, $display(\"m\")) ##1 b; endproperty\n"
    "  property pu; @(posedge clk) (a, f()) ##1 b; endproperty\n"
    "  property pi; int n; @(posedge clk) (a, n = 0, n++, n--) ##1 b; "
    "endproperty\n"
    "  property pc; int n; @(posedge clk) (a ##1 b, n = 1) ##1 a; endproperty\n"
    "  sequence sm; int n; (a, n = 1, $display(\"m\")) ##1 b; endsequence\n"
    "  k1: assert property (@(posedge clk) (a, $display(\"m\")) ##1 b);\n"
    "endmodule\n";

TEST_F(SequenceInstsEverywhere, DISABLED_ATaskCallItemIsReachedAsATfCall) {
  Run(kMatchItems);
  const std::vector<vpiHandle> kItems = ItemsOfFirstOperand(PropertyBody("pt"));
  ASSERT_EQ(kItems.size(), 1u);
  EXPECT_EQ(vpi_get(vpiType, kItems[0]), vpiSysTaskCall);
  EXPECT_EQ(CalleeOf(kItems[0]), "$display");
}

TEST_F(SequenceInstsEverywhere, DISABLED_AFunctionCallItemIsReachedAsATfCall) {
  Run(kMatchItems);
  const std::vector<vpiHandle> kItems = ItemsOfFirstOperand(PropertyBody("pu"));
  ASSERT_EQ(kItems.size(), 1u);
  EXPECT_EQ(vpi_get(vpiType, kItems[0]), vpiFuncCall);
  EXPECT_EQ(CalleeOf(kItems[0]), "f");
}

TEST_F(SequenceInstsEverywhere, AnIncrementAndADecrementAreAssignments) {
  Run(kMatchItems);
  const std::vector<vpiHandle> kItems = ItemsOfFirstOperand(PropertyBody("pi"));
  ASSERT_EQ(kItems.size(), 3u);
  for (vpiHandle item : kItems) {
    EXPECT_EQ(vpi_get(vpiType, item), vpiAssignment);
    EXPECT_EQ(NameOf(vpi_handle(vpiLhs, item)), "n");
  }
}

TEST_F(SequenceInstsEverywhere, DISABLED_ASequenceBodysOperandReachesEachItem) {
  Run(kMatchItems);
  const std::vector<vpiHandle> kItems = ItemsOfFirstOperand(
      vpi_handle(vpiExpr, Named(vpiSequenceDecl, By("top"), "sm")));
  ASSERT_EQ(kItems.size(), 2u);
  EXPECT_EQ(vpi_get(vpiType, kItems[0]), vpiAssignment);
  EXPECT_EQ(vpi_get(vpiType, kItems[1]), vpiSysTaskCall);
}

TEST_F(SequenceInstsEverywhere,
       DISABLED_AnInlineAssertionsOperandReachesItsItem) {
  Run(kMatchItems);
  const std::vector<vpiHandle> kItems = ItemsOfFirstOperand(PropertyOf("k1"));
  ASSERT_EQ(kItems.size(), 1u);
  EXPECT_EQ(vpi_get(vpiType, kItems[0]), vpiSysTaskCall);
}

TEST_F(SequenceInstsEverywhere,
       DISABLED_ACompositeOperandsOperationReachesItsItem) {
  Run(kMatchItems);
  const std::vector<vpiHandle> kParts = OperandsOf(PropertyBody("pc"));
  ASSERT_FALSE(kParts.empty());
  EXPECT_EQ(OpOf(kParts.front()), vpiCycleDelayOp);
  const std::vector<vpiHandle> kItems = ObjectsOf(vpiMatchItem, kParts.front());
  ASSERT_EQ(kItems.size(), 1u);
  EXPECT_EQ(vpi_get(vpiType, kItems[0]), vpiAssignment);
}

TEST_F(SequenceInstsEverywhere, AMemberSelectOperandIsTheMembersVariable) {
  Run("module top; logic clk, b; struct packed { logic f; } st;\n"
      "  e1: assert property (@(posedge clk) st.f ##1 b);\n"
      "endmodule\n");
  const std::vector<vpiHandle> kParts = OperandsOf(PropertyOf("e1"));
  ASSERT_FALSE(kParts.empty());
  ASSERT_NE(kParts.front(), nullptr);
  EXPECT_EQ(vpi_get(vpiType, kParts.front()), vpiLogicVar);
  EXPECT_STREQ(vpi_get_str(vpiFullName, kParts.front()), "top.st.f");
}

constexpr const char* kFourKindAssertions =
    "  sequence s0; a; endsequence\n"
    "  xop: assert property (@(posedge clk) a ##1 b);\n"
    "  xinst: assert property (@(posedge clk) s0);\n"
    "  xdist: assert property (@(posedge clk) a dist {0 := 1, 1 := 3});\n"
    "  xexpr: assert property (@(posedge clk) a);\n";

TEST_F(SequenceInstsEverywhere, AnInterfacesAssertionsTakeAllFourKinds) {
  Run(std::string("interface ifc; logic clk, a, b;\n") + kFourKindAssertions +
      "endinterface\nmodule top; ifc i0(); endmodule\n");
  ExpectFourKinds(nullptr, "x");
}

TEST_F(SequenceInstsEverywhere, AProgramsAssertionsTakeAllFourKinds) {
  Run(std::string("program prg; logic clk, a, b;\n") + kFourKindAssertions +
      "endprogram\nmodule top; prg pr0(); endmodule\n");
  ExpectFourKinds(nullptr, "x");
}

TEST_F(SequenceInstsEverywhere, ACheckersAssertionsTakeAllFourKinds) {
  Run(std::string("checker chk; logic clk, a, b;\n") + kFourKindAssertions +
      "endchecker\nmodule top; chk k0(); endmodule\n");
  ExpectFourKinds(nullptr, "x");
}

constexpr const char* kFourKindBodies =
    "  sequence s0; a; endsequence\n"
    "  sequence xop; a ##1 b; endsequence\n"
    "  sequence xinst; s0; endsequence\n"
    "  sequence xdist; a dist {0 := 1, 1 := 3}; endsequence\n"
    "  sequence xexpr; a; endsequence\n";

TEST_F(SequenceInstsEverywhere, APackagesSequenceBodiesTakeAllFourKinds) {
  Run(std::string("package pk; logic a, b;\n") + kFourKindBodies +
      "endpackage\nmodule top; endmodule\n");
  ExpectFourKinds(By("pk"), "x");
}

TEST_F(SequenceInstsEverywhere,
       DISABLED_ACompilationUnitsBodiesTakeAllFourKinds) {
  Run(std::string("logic a, b;\n") + kFourKindBodies +
      "module top; endmodule\n");
  ExpectFourKinds(Named(vpiPackage, nullptr, "$unit"), "x");
}

}  // namespace
}  // namespace delta
