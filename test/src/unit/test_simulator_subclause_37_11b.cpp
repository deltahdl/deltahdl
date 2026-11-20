#include <gtest/gtest.h>

#include <string>
#include <utility>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

using Bounds = std::vector<std::pair<int, int>>;

struct Override {
  std::string lhs;
  int rhs;
  bool operator==(const Override&) const = default;
};

class InstanceArrayKindsOfARun : public VpiDesignRun {
 protected:
  static int ValueOf(vpiHandle obj) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(obj, &value);
    return value.value.integer;
  }

  static vpiHandle ArrayOfKind(int relation, int kind) {
    for (vpiHandle array : ObjectsOf(relation, By("top"))) {
      if (vpi_get(vpiType, array) == kind) return array;
    }
    return nullptr;
  }

  static vpiHandle Gates() {
    return ArrayOfKind(vpiPrimitiveArray, vpiGateArray);
  }
  static vpiHandle Switches() {
    return ArrayOfKind(vpiPrimitiveArray, vpiSwitchArray);
  }
  static vpiHandle Udps() {
    return ArrayOfKind(vpiPrimitiveArray, vpiUdpArray);
  }

  static Bounds RangesOf(vpiHandle array) {
    Bounds bounds;
    for (vpiHandle range : ObjectsOf(vpiRange, array)) {
      bounds.emplace_back(ValueOf(vpi_handle(vpiLeftRange, range)),
                          ValueOf(vpi_handle(vpiRightRange, range)));
    }
    return bounds;
  }

  static std::pair<int, int> LeftmostOf(vpiHandle array) {
    return {ValueOf(vpi_handle(vpiLeftRange, array)),
            ValueOf(vpi_handle(vpiRightRange, array))};
  }

  static std::vector<Override> OverridesOf(vpiHandle array) {
    std::vector<Override> overrides;
    for (vpiHandle assign : ObjectsOf(vpiParamAssign, array)) {
      vpiHandle lhs = vpi_handle(vpiLhs, assign);
      s_vpi_value value = {};
      value.format = vpiIntVal;
      vpi_get_value(vpi_handle(vpiRhs, assign), &value);
      overrides.push_back({lhs == nullptr ? "" : vpi_get_str(vpiFullName, lhs),
                           value.value.integer});
    }
    return overrides;
  }

  static std::vector<std::string> OperandsOf(vpiHandle array) {
    std::vector<std::string> operands;
    vpiHandle list = vpi_handle(vpiExpr, array);
    if (list == nullptr || vpi_get(vpiOpType, list) != vpiListOp) return {};
    for (vpiHandle operand : ObjectsOf(vpiOperand, list)) {
      const char* name = vpi_get_str(vpiName, operand);
      operands.emplace_back(
          name == nullptr ? "#" + std::to_string(vpi_get(vpiType, operand))
                          : name);
    }
    return operands;
  }
};

constexpr const char* kArraysOfEveryKind =
    "primitive my_and(o, a, b);\n"
    "  output o; input a, b;\n"
    "  table 0 ? : 0; ? 0 : 0; 1 1 : 1; endtable\n"
    "endprimitive\n"
    "interface ifc #(parameter int P = 1, parameter int Q = 2)\n"
    "  (input logic c); endinterface\n"
    "program prg #(parameter int P = 1, parameter int Q = 2)\n"
    "  (input logic c); endprogram\n"
    "module sub; endmodule\n"
    "module mid; sub sa[1:0] (); endmodule\n"
    "module top; logic c; wire [1:0] y, z, o; logic [1:0] a, b, i;\n"
    "  sub arr[2:4] ();\n"
    "  sub mu[1:0][2:4] ();\n"
    "  ifc #(.P(3)) is[1:0] (.c(c));\n"
    "  ifc #(3, 4) js[0:1] (c);\n"
    "  ifc ii[1:0][2:3] (.c(c));\n"
    "  prg #(.P(3)) ps[1:0] (.c(c));\n"
    "  prg #(3, 4) qs[0:1] (c);\n"
    "  prg pp[1:0][2:3] (.c(c));\n"
    "  and g[1:0] (y, a, b);\n"
    "  nmos m[1:0] (o, i, c);\n"
    "  my_and u[1:0] (z, a, b);\n"
    "  mid md ();\n"
    "  sub lone ();\n"
    "endmodule\n";

TEST_F(InstanceArrayKindsOfARun, EveryInstanceArrayHasItsNameAndFullName) {
  Run(kArraysOfEveryKind);
  struct Named {
    vpiHandle array;
    const char* name;
    const char* full;
  };
  for (const Named& n :
       {Named{By("top.arr"), "arr", "top.arr"},
        Named{By("top.is"), "is", "top.is"},
        Named{By("top.ps"), "ps", "top.ps"}, Named{Gates(), "g", "top.g"},
        Named{Switches(), "m", "top.m"}, Named{Udps(), "u", "top.u"},
        Named{By("top.md.sa"), "sa", "top.md.sa"}}) {
    ASSERT_NE(n.array, nullptr) << n.full;
    EXPECT_STREQ(vpi_get_str(vpiName, n.array), n.name) << n.full;
    EXPECT_STREQ(vpi_get_str(vpiFullName, n.array), n.full) << n.full;
  }
}

TEST_F(InstanceArrayKindsOfARun, EveryInstanceArrayCountsEveryElement) {
  Run(kArraysOfEveryKind);
  EXPECT_EQ(vpi_get(vpiSize, By("top.ps")), 2);
  EXPECT_EQ(vpi_get(vpiSize, Switches()), 2);
}

TEST_F(InstanceArrayKindsOfARun,
       DISABLED_AMultidimensionalArrayCountsEveryElement) {
  Run(kArraysOfEveryKind);
  EXPECT_EQ(vpi_get(vpiSize, By("top.mu")), 6);
  EXPECT_EQ(vpi_get(vpiSize, By("top.pp")), 4);
}

TEST_F(InstanceArrayKindsOfARun, InterfaceAndProgramElementsAreReachedByIndex) {
  Run(kArraysOfEveryKind);
  PLI_INT32 one[] = {0};
  PLI_INT32 two[] = {1, 3};
  for (const char* kind : {"is", "ps"}) {
    std::string name = std::string("top.") + kind;
    vpiHandle array = By(name);
    ASSERT_NE(array, nullptr) << name;
    EXPECT_EQ(VpiObjectOf(vpi_handle_by_index(array, 1)),
              VpiObjectOf(By(name + "[1]")))
        << name;
    EXPECT_EQ(VpiObjectOf(vpi_handle_by_multi_index(array, 1, one)),
              VpiObjectOf(By(name + "[0]")))
        << name;
  }
  for (const char* kind : {"ii", "pp"}) {
    std::string name = std::string("top.") + kind;
    vpiHandle array = By(name);
    ASSERT_NE(array, nullptr) << name;
    EXPECT_EQ(VpiObjectOf(vpi_handle_by_multi_index(array, 2, two)),
              VpiObjectOf(By(name + "[1][3]")))
        << name;
  }
}

TEST_F(InstanceArrayKindsOfARun, PrimitiveElementsAreReachedByMultiIndex) {
  Run(kArraysOfEveryKind);
  PLI_INT32 first[] = {1};
  for (vpiHandle array : {Gates(), Switches(), Udps()}) {
    ASSERT_NE(array, nullptr);
    vpiHandle element = vpi_handle_by_multi_index(array, 1, first);
    ASSERT_NE(element, nullptr) << vpi_get_str(vpiName, array);
    EXPECT_EQ(VpiObjectOf(element), VpiObjectOf(vpi_handle_by_index(array, 1)))
        << vpi_get_str(vpiName, array);
  }
}

TEST_F(InstanceArrayKindsOfARun, EveryInstanceArrayIteratesARangePerDimension) {
  Run(kArraysOfEveryKind);
  EXPECT_EQ(RangesOf(By("top.arr")), (Bounds{{2, 4}}));
  EXPECT_EQ(RangesOf(By("top.is")), (Bounds{{1, 0}}));
  EXPECT_EQ(RangesOf(By("top.ps")), (Bounds{{1, 0}}));
  EXPECT_EQ(RangesOf(By("top.ii")), (Bounds{{1, 0}, {2, 3}}));
  EXPECT_EQ(RangesOf(By("top.pp")), (Bounds{{1, 0}, {2, 3}}));
  for (vpiHandle array : {Gates(), Switches(), Udps()}) {
    ASSERT_NE(array, nullptr);
    EXPECT_EQ(RangesOf(array), (Bounds{{1, 0}})) << vpi_get_str(vpiName, array);
  }
}

TEST_F(InstanceArrayKindsOfARun, EveryInstanceArrayHasItsLeftmostBounds) {
  Run(kArraysOfEveryKind);
  const std::pair<int, int> kOneZero = {1, 0};
  EXPECT_EQ(LeftmostOf(By("top.js")), (std::pair<int, int>{0, 1}));
  for (const char* name : {"top.is", "top.ps", "top.ii", "top.pp"}) {
    EXPECT_EQ(LeftmostOf(By(name)), kOneZero) << name;
  }
  for (vpiHandle array : {Gates(), Switches(), Udps()}) {
    ASSERT_NE(array, nullptr);
    EXPECT_EQ(LeftmostOf(array), kOneZero) << vpi_get_str(vpiName, array);
  }
}

TEST_F(InstanceArrayKindsOfARun, APrimitiveArrayIteratesItsElementsInOrder) {
  Run(kArraysOfEveryKind);
  for (vpiHandle array : {Gates(), Switches(), Udps()}) {
    ASSERT_NE(array, nullptr);
    std::vector<vpiHandle> elements = ObjectsOf(vpiPrimitive, array);
    ASSERT_EQ(elements.size(), 2U) << vpi_get_str(vpiName, array);
    EXPECT_EQ(VpiObjectOf(elements[0]),
              VpiObjectOf(vpi_handle_by_index(array, 0)));
    EXPECT_EQ(VpiObjectOf(elements[1]),
              VpiObjectOf(vpi_handle_by_index(array, 1)));
  }
  vpiHandle switches = Switches();
  ASSERT_NE(switches, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiPrimitiveArray,
                                   vpi_handle_by_index(switches, 1))),
            VpiObjectOf(switches));
}

TEST_F(InstanceArrayKindsOfARun, APrimitiveArrayReachesTheDelayWritten) {
  Run("module top; wire [1:0] o, p, y; logic [1:0] i, a, b; logic c;\n"
      "  nmos #3 md[1:0] (o, i, c);\n"
      "  nmos m[1:0] (p, i, c);\n"
      "  and g[1:0] (y, a, b);\n"
      "endmodule\n");
  vpiHandle md = nullptr;
  vpiHandle plain = nullptr;
  vpiHandle gates = nullptr;
  for (vpiHandle array : ObjectsOf(vpiPrimitiveArray, By("top"))) {
    std::string name = vpi_get_str(vpiName, array);
    if (name == "md") md = array;
    if (name == "m") plain = array;
    if (name == "g") gates = array;
  }
  ASSERT_NE(md, nullptr);
  vpiHandle delay = vpi_handle(vpiDelay, md);
  ASSERT_NE(delay, nullptr);
  EXPECT_EQ(VpiObjectOf(delay),
            VpiObjectOf(vpi_handle(vpiDelay, vpi_handle_by_index(md, 0))));
  EXPECT_EQ(vpi_handle(vpiDelay, plain), nullptr);
  EXPECT_EQ(vpi_handle(vpiDelay, gates), nullptr);
}

TEST_F(InstanceArrayKindsOfARun, InterfaceAndProgramArraysReachTheirOverrides) {
  Run(kArraysOfEveryKind);
  EXPECT_EQ(OverridesOf(By("top.is")),
            (std::vector<Override>{{"top.is[1].P", 3}}));
  EXPECT_EQ(OverridesOf(By("top.js")),
            (std::vector<Override>{{"top.js[0].P", 3}, {"top.js[0].Q", 4}}));
  EXPECT_EQ(OverridesOf(By("top.ps")),
            (std::vector<Override>{{"top.ps[1].P", 3}}));
  EXPECT_EQ(OverridesOf(By("top.qs")),
            (std::vector<Override>{{"top.qs[0].P", 3}, {"top.qs[0].Q", 4}}));
}

TEST_F(InstanceArrayKindsOfARun, AModuleArraysConnectionsFollowTheSource) {
  Run("module sub (input [3:0] a, output [3:0] o); assign o = a; endmodule\n"
      "module top; logic [3:0] w; wire [3:0] y; logic [7:0] wide;\n"
      "  logic [3:0] h, l; wire [7:0] out;\n"
      "  sub nu[1:0] (.o(y), .a(w));\n"
      "  sub ou[1:0] (w, y);\n"
      "  sub pu[1:0] (.a(wide[7:0]), .o(out));\n"
      "  sub cu[1:0] (.a({h, l}), .o(out));\n"
      "endmodule\n");
  EXPECT_EQ(OperandsOf(By("top.nu")), (std::vector<std::string>{"y", "w"}));
  EXPECT_EQ(OperandsOf(By("top.ou")), (std::vector<std::string>{"w", "y"}));
  vpiHandle part = vpi_handle(vpiExpr, By("top.pu"));
  ASSERT_NE(part, nullptr);
  std::vector<vpiHandle> parts = ObjectsOf(vpiOperand, part);
  ASSERT_EQ(parts.size(), 2U);
  EXPECT_EQ(vpi_get(vpiType, parts[0]), vpiPartSelect);
  vpiHandle cat = vpi_handle(vpiExpr, By("top.cu"));
  ASSERT_NE(cat, nullptr);
  std::vector<vpiHandle> cats = ObjectsOf(vpiOperand, cat);
  ASSERT_EQ(cats.size(), 2U);
  EXPECT_EQ(vpi_get(vpiType, cats[0]), vpiOperation);
  EXPECT_EQ(vpi_get(vpiOpType, cats[0]), vpiConcatOp);
}

TEST_F(InstanceArrayKindsOfARun,
       InterfaceAndProgramArraysReachTheConnectionsWritten) {
  Run(kArraysOfEveryKind);
  EXPECT_EQ(OperandsOf(By("top.is")), std::vector<std::string>{"c"});
  EXPECT_EQ(OperandsOf(By("top.ps")), std::vector<std::string>{"c"});
}

TEST_F(InstanceArrayKindsOfARun,
       DISABLED_EveryPrimitiveArrayReachesTheTerminalsWritten) {
  Run(kArraysOfEveryKind);
  EXPECT_EQ(OperandsOf(Gates()), (std::vector<std::string>{"y", "a", "b"}));
  EXPECT_EQ(OperandsOf(Switches()), (std::vector<std::string>{"o", "i", "c"}));
  EXPECT_EQ(OperandsOf(Udps()), (std::vector<std::string>{"z", "a", "b"}));
}

TEST_F(InstanceArrayKindsOfARun, OnlyPrimitiveArraysArePrimitiveArrays) {
  Run(kArraysOfEveryKind);
  EXPECT_EQ(NamesOf(vpiPrimitiveArray, By("top")),
            (std::vector<std::string>{"g", "m", "u"}));
}

TEST_F(InstanceArrayKindsOfARun, AProgramArrayIsAProgramArray) {
  Run(kArraysOfEveryKind);
  EXPECT_EQ(vpi_get(vpiType, By("top.ps")), vpiProgramArray);
}

TEST_F(InstanceArrayKindsOfARun, AModuleIteratesEveryInstanceArrayItHolds) {
  Run(kArraysOfEveryKind);
  EXPECT_EQ(NamesOf(vpiInstanceArray, By("top")),
            (std::vector<std::string>{"arr", "g", "ii", "is", "js", "m", "mu",
                                      "pp", "ps", "qs", "u"}));
}

}  // namespace
}  // namespace delta
