#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class PrimitiveRulesOfARun : public VpiDesignRun {
 protected:
  static vpiHandle Prim(const char* scope, const char* name) {
    return Named(vpiPrimitive, By(scope), name);
  }

  static std::vector<int> TermIntsOf(vpiHandle prim, int property) {
    std::vector<int> values;
    for (vpiHandle term : ObjectsOf(vpiPrimTerm, prim)) {
      values.push_back(vpi_get(property, term));
    }
    return values;
  }

  static vpiHandle TermExpr(vpiHandle prim, std::size_t index) {
    const std::vector<vpiHandle> kTerms = ObjectsOf(vpiPrimTerm, prim);
    return index < kTerms.size() ? vpi_handle(vpiExpr, kTerms[index]) : nullptr;
  }

  static std::string FullNameOf(vpiHandle obj) {
    const char* name = obj == nullptr ? nullptr : vpi_get_str(vpiFullName, obj);
    return name == nullptr ? "" : name;
  }

  static std::string DefNameOf(vpiHandle obj) {
    const char* name = obj == nullptr ? nullptr : vpi_get_str(vpiDefName, obj);
    return name == nullptr ? "" : name;
  }
};

constexpr const char* kInvUdp =
    "primitive inv_udp(o, a);\n"
    "  output o; input a;\n"
    "  table 0 : 1; 1 : 0; endtable\n"
    "endprimitive\n";

constexpr const char* kLatchUdp =
    "primitive latch_udp(q, d, en);\n"
    "  output reg q; input d, en;\n"
    "  table\n"
    "    0 1 : ? : 0;\n"
    "    1 1 : ? : 1;\n"
    "    ? 0 : ? : -;\n"
    "  endtable\n"
    "endprimitive\n";

constexpr const char* kArrays =
    "module m; wire y, o, w; logic a, c;\n"
    "  and g(y, a, a);\n"
    "  nmos n(o, a, c);\n"
    "  inv_udp u(w, a);\n"
    "endmodule\n"
    "module top; wire y, o, w; wire [1:0] ya, yb, yc;\n"
    "  logic a, b, c; logic [1:0] aa, ca;\n"
    "  and g1(y, a, b);\n"
    "  nmos m1(o, a, c);\n"
    "  inv_udp u1(w, a);\n"
    "  and g[1:0] (ya, aa, aa);\n"
    "  nmos s[1:0] (yb, aa, ca);\n"
    "  inv_udp u[1:0] (yc, aa);\n"
    "  m sub();\n"
    "endmodule\n";

TEST_F(PrimitiveRulesOfARun, AModuleIteratesEachConcreteKindApart) {
  Run(std::string(kInvUdp) +
      "module top; wire y1, y2, o, w1, w2, v1, v2; logic a, b, c;\n"
      "  and g1(y1, a, b);\n"
      "  or g2(y2, a, b);\n"
      "  nmos m1(o, a, c);\n"
      "  tran t1(v1, v2);\n"
      "  inv_udp u1(w1, a);\n"
      "  inv_udp u2(w2, b);\n"
      "endmodule\n");
  EXPECT_EQ(NamesOf(vpiGate, By("top")),
            (std::vector<std::string>{"g1", "g2"}));
  EXPECT_EQ(NamesOf(vpiSwitch, By("top")),
            (std::vector<std::string>{"m1", "t1"}));
  EXPECT_EQ(NamesOf(vpiUdp, By("top")), (std::vector<std::string>{"u1", "u2"}));
}

TEST_F(PrimitiveRulesOfARun, EveryPrimitiveReachesTheModuleHoldingIt) {
  Run(std::string(kInvUdp) + kArrays);
  for (const char* name : {"g1", "m1", "u1", "g[1]", "s[0]", "u[1]"}) {
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiModule, Prim("top", name))),
              VpiObjectOf(By("top")))
        << name;
  }
  for (const char* name : {"g", "n", "u"}) {
    vpiHandle module = vpi_handle(vpiModule, Prim("top.sub", name));
    ASSERT_NE(module, nullptr) << name;
    EXPECT_EQ(VpiObjectOf(module), VpiObjectOf(By("top.sub"))) << name;
  }
}

TEST_F(PrimitiveRulesOfARun, AnArrayElementIsAnInstanceOfItsKeywordOrUdp) {
  Run(std::string(kInvUdp) + kArrays);
  EXPECT_EQ(DefNameOf(Prim("top", "g[1]")), "and");
  EXPECT_EQ(DefNameOf(Prim("top", "s[0]")), "nmos");
  EXPECT_EQ(DefNameOf(Prim("top", "u[1]")), "inv_udp");
}

TEST_F(PrimitiveRulesOfARun, APrimitiveReportsItsFullName) {
  Run(std::string(kInvUdp) + kArrays);
  EXPECT_EQ(FullNameOf(Prim("top", "g1")), "top.g1");
  EXPECT_EQ(FullNameOf(Prim("top", "m1")), "top.m1");
  EXPECT_EQ(FullNameOf(Prim("top", "u1")), "top.u1");
  EXPECT_EQ(FullNameOf(Prim("top", "g[0]")), "top.g[0]");
  EXPECT_EQ(FullNameOf(Prim("top.sub", "g")), "top.sub.g");
}

TEST_F(PrimitiveRulesOfARun, AnArrayElementIsAnArrayMember) {
  Run(std::string(kInvUdp) + kArrays);
  for (const char* name : {"g[0]", "s[1]", "u[0]"}) {
    vpiHandle prim = Prim("top", name);
    ASSERT_NE(prim, nullptr) << name;
    EXPECT_EQ(vpi_get(vpiArrayMember, prim), 1) << name;
  }
}

TEST_F(PrimitiveRulesOfARun, DISABLED_AnArrayElementReportsTheDeprecatedArray) {
  Run(std::string(kInvUdp) + kArrays);
  for (const char* name : {"g[0]", "s[1]", "u[0]"}) {
    vpiHandle prim = Prim("top", name);
    ASSERT_NE(prim, nullptr) << name;
    EXPECT_EQ(vpi_get(vpiArray, prim), 1) << name;
  }
}

TEST_F(PrimitiveRulesOfARun, AStandalonePrimitiveIsNoArrayMember) {
  Run(std::string(kInvUdp) + kArrays);
  for (const char* name : {"g1", "m1", "u1"}) {
    vpiHandle prim = Prim("top", name);
    ASSERT_NE(prim, nullptr) << name;
    EXPECT_EQ(vpi_get(vpiArrayMember, prim), 0) << name;
    EXPECT_EQ(vpi_get(vpiArray, prim), 0) << name;
  }
}

TEST_F(PrimitiveRulesOfARun, AUdpOrSwitchArrayElementReachesItsIndex) {
  Run(std::string(kInvUdp) + kArrays);
  for (const char* name : {"u[1]", "s[1]"}) {
    vpiHandle index = vpi_handle(vpiIndex, Prim("top", name));
    ASSERT_NE(index, nullptr) << name;
    EXPECT_EQ(IntegerOf(index), 1) << name;
  }
  vpiHandle index = vpi_handle(vpiIndex, Prim("top", "s[0]"));
  ASSERT_NE(index, nullptr);
  EXPECT_EQ(IntegerOf(index), 0);
}

TEST_F(PrimitiveRulesOfARun, AStandalonePrimitiveReachesNoIndex) {
  Run(std::string(kInvUdp) + kArrays);
  for (const char* name : {"g1", "m1", "u1"}) {
    vpiHandle prim = Prim("top", name);
    ASSERT_NE(prim, nullptr) << name;
    EXPECT_EQ(vpi_handle(vpiIndex, prim), nullptr) << name;
  }
}

TEST_F(PrimitiveRulesOfARun, EachUdpInstanceReachesTheDefnItNames) {
  Run(std::string(kInvUdp) + kLatchUdp +
      "module top; wire w1, w2, q1; wire [1:0] wa, qa;\n"
      "  logic a, d, en; logic [1:0] aa, da, ea;\n"
      "  inv_udp u1(w1, a);\n"
      "  inv_udp u2(w2, a);\n"
      "  latch_udp l1(q1, d, en);\n"
      "  inv_udp ua[1:0] (wa, aa);\n"
      "  latch_udp la[1:0] (qa, da, ea);\n"
      "endmodule\n");
  vpiHandle inv = vpi_handle(vpiUdpDefn, Prim("top", "u1"));
  vpiHandle latch = vpi_handle(vpiUdpDefn, Prim("top", "l1"));
  ASSERT_NE(inv, nullptr);
  ASSERT_NE(latch, nullptr);
  EXPECT_EQ(vpi_get(vpiType, latch), vpiUdpDefn);
  EXPECT_EQ(DefNameOf(latch), "latch_udp");
  EXPECT_EQ(DefNameOf(inv), "inv_udp");
  EXPECT_NE(VpiObjectOf(inv), VpiObjectOf(latch));
  for (const char* name : {"u2", "ua[0]", "ua[1]"}) {
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiUdpDefn, Prim("top", name))),
              VpiObjectOf(inv))
        << name;
  }
  for (const char* name : {"la[0]", "la[1]"}) {
    vpiHandle defn = vpi_handle(vpiUdpDefn, Prim("top", name));
    ASSERT_NE(defn, nullptr) << name;
    EXPECT_EQ(vpi_get(vpiType, defn), vpiUdpDefn) << name;
    EXPECT_EQ(VpiObjectOf(defn), VpiObjectOf(latch)) << name;
  }
}

constexpr const char* kShapes =
    "module top; wire w, v, x, y, z; logic a, b, c, d;\n"
    "  and g3(w, a, b, c);\n"
    "  nmos m_nmos(w, a, c); pmos m_pmos(w, a, c);\n"
    "  rnmos m_rnmos(w, a, c); rpmos m_rpmos(w, a, c);\n"
    "  cmos m_cmos(w, a, b, c); rcmos m_rcmos(w, a, b, c);\n"
    "  bufif0 b_bufif0(w, a, c); bufif1 b_bufif1(w, a, c);\n"
    "  notif0 b_notif0(w, a, c); notif1 b_notif1(w, a, c);\n"
    "  tran t_tran(v, x); rtran t_rtran(v, x);\n"
    "  tranif1 t_tranif1(v, x, c);\n"
    "  pullup p_pullup(y); pulldown p_pulldown(z);\n"
    "  latch_udp l(y, a, d);\n"
    "endmodule\n";

TEST_F(PrimitiveRulesOfARun, APrimitivesSizeIsItsNumberOfInputs) {
  Run(std::string(kLatchUdp) + kShapes);
  const struct {
    const char* name;
    int inputs;
  } kCases[] = {{"g3", 3},       {"m_cmos", 3},    {"m_rcmos", 3},
                {"b_bufif0", 2}, {"b_bufif1", 2},  {"b_notif0", 2},
                {"b_notif1", 2}, {"t_tran", 0},    {"t_rtran", 0},
                {"l", 2},        {"p_pulldown", 0}};
  for (const auto& c : kCases) {
    vpiHandle prim = Prim("top", c.name);
    ASSERT_NE(prim, nullptr) << c.name;
    EXPECT_EQ(vpi_get(vpiSize, prim), c.inputs) << c.name;
  }
}

TEST_F(PrimitiveRulesOfARun, ASwitchsTerminalsRunAsItDrivesThem) {
  Run(std::string(kLatchUdp) + kShapes);
  const std::vector<int> kMos = {vpiOutput, vpiInput, vpiInput};
  const std::vector<int> kCmos = {vpiOutput, vpiInput, vpiInput, vpiInput};
  const std::vector<int> kTran = {vpiInout, vpiInout};
  const struct {
    const char* name;
    const std::vector<int>* directions;
  } kCases[] = {{"m_nmos", &kMos},  {"m_pmos", &kMos},  {"m_rnmos", &kMos},
                {"m_rpmos", &kMos}, {"m_cmos", &kCmos}, {"m_rcmos", &kCmos},
                {"t_tran", &kTran}, {"t_rtran", &kTran}};
  for (const auto& c : kCases) {
    EXPECT_EQ(TermIntsOf(Prim("top", c.name), vpiDirection), *c.directions)
        << c.name;
  }
}

TEST_F(PrimitiveRulesOfARun, EveryPrimitivesTermsCountFromZero) {
  Run(std::string(kLatchUdp) + kInvUdp + kShapes +
      "module arr; wire [1:0] y; logic [1:0] a, b; wire w;\n"
      "  and g[1:0] (y, a, b);\n"
      "  inv_udp u(w, a[0]);\n"
      "endmodule\n"
      "module both; top t(); arr a(); endmodule\n");
  const struct {
    const char* scope;
    const char* name;
    std::vector<int> indexes;
  } kCases[] = {{"both.t", "g3", {0, 1, 2, 3}},
                {"both.t", "m_nmos", {0, 1, 2}},
                {"both.t", "m_cmos", {0, 1, 2, 3}},
                {"both.t", "t_tran", {0, 1}},
                {"both.t", "t_tranif1", {0, 1, 2}},
                {"both.t", "p_pullup", {0}},
                {"both.t", "p_pulldown", {0}},
                {"both.t", "l", {0, 1, 2}},
                {"both.a", "u", {0, 1}},
                {"both.a", "g[1]", {0, 1, 2}}};
  for (const auto& c : kCases) {
    EXPECT_EQ(TermIntsOf(Prim(c.scope, c.name), vpiTermIndex), c.indexes)
        << c.name;
  }
}

TEST_F(PrimitiveRulesOfARun, ASwitchsTermsReachTheirSwitch) {
  Run(std::string(kLatchUdp) + kShapes);
  for (const char* name : {"t_tranif1", "m_nmos"}) {
    vpiHandle prim = Prim("top", name);
    const std::vector<vpiHandle> kTerms = ObjectsOf(vpiPrimTerm, prim);
    ASSERT_EQ(kTerms.size(), 3U) << name;
    for (vpiHandle term : kTerms) {
      EXPECT_EQ(VpiObjectOf(vpi_handle(vpiPrimitive, term)), VpiObjectOf(prim))
          << name;
    }
  }
}

constexpr const char* kTerminalForms =
    "module top; wire y1, y2, y3, y4, y5, y6, o, v1, v2;\n"
    "  logic [3:0] v; logic c, i, d; wire w [2]; int k; integer n;\n"
    "  and g1(y1, 1'b1, c);\n"
    "  and g2(y2, v[2], c);\n"
    "  and g3(y3, v[1:1], c);\n"
    "  and g4(y4, {c}, c);\n"
    "  and g5(y5, w[k], c);\n"
    "  and g6(y6, n[1], c);\n"
    "  nmos m(o, i, d);\n"
    "  tran t(v1, v2);\n"
    "endmodule\n";

TEST_F(PrimitiveRulesOfARun, AConstantTerminalReachesAConstant) {
  Run(kTerminalForms);
  vpiHandle expr = TermExpr(Prim("top", "g1"), 1);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(vpi_get(vpiType, expr), vpiConstant);
  EXPECT_EQ(IntegerOf(expr), 1);
}

TEST_F(PrimitiveRulesOfARun, ASelectTerminalReachesItsSelectOrBit) {
  Run(kTerminalForms);
  vpiHandle bit = TermExpr(Prim("top", "g2"), 1);
  ASSERT_NE(bit, nullptr);
  EXPECT_EQ(vpi_get(vpiType, bit), vpiVarBit);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, bit)), VpiObjectOf(By("top.v")));
  vpiHandle int_bit = TermExpr(Prim("top", "g6"), 1);
  ASSERT_NE(int_bit, nullptr);
  EXPECT_EQ(vpi_get(vpiType, int_bit), vpiBitSelect);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, int_bit)),
            VpiObjectOf(By("top.n")));
  vpiHandle part = TermExpr(Prim("top", "g3"), 1);
  ASSERT_NE(part, nullptr);
  EXPECT_EQ(vpi_get(vpiType, part), vpiPartSelect);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, part)), VpiObjectOf(By("top.v")));
}

TEST_F(PrimitiveRulesOfARun, AConcatenationTerminalReachesItsOperation) {
  Run(kTerminalForms);
  EXPECT_EQ(OpOf(TermExpr(Prim("top", "g4"), 1)), vpiConcatOp);
}

TEST_F(PrimitiveRulesOfARun,
       DISABLED_ATerminalOfAVariableIndexReachesAnExpression) {
  Run(kTerminalForms);
  EXPECT_NE(TermExpr(Prim("top", "g5"), 1), nullptr);
}

TEST_F(PrimitiveRulesOfARun, ASwitchsTerminalsReachWhatTheyConnect) {
  Run(kTerminalForms);
  const struct {
    const char* name;
    std::vector<const char*> connected;
  } kCases[] = {{"m", {"top.o", "top.i", "top.d"}},
                {"t", {"top.v1", "top.v2"}}};
  for (const auto& c : kCases) {
    vpiHandle prim = Prim("top", c.name);
    ASSERT_EQ(ObjectsOf(vpiPrimTerm, prim).size(), c.connected.size())
        << c.name;
    for (std::size_t n = 0; n < c.connected.size(); ++n) {
      EXPECT_EQ(VpiObjectOf(TermExpr(prim, n)), VpiObjectOf(By(c.connected[n])))
          << c.name << " " << n;
    }
  }
}

TEST_F(PrimitiveRulesOfARun, ASwitchReachesTheDelayItIsWrittenWith) {
  Run("module top; wire o, v1, v2; logic i, n, p, c;\n"
      "  cmos #(2, 3, 4) m(o, i, n, p);\n"
      "  rtranif1 #3 t(v1, v2, c);\n"
      "endmodule\n");
  vpiHandle list = vpi_handle(vpiDelay, Prim("top", "m"));
  ASSERT_EQ(OpOf(list), vpiListOp);
  std::vector<int> values;
  for (vpiHandle operand : OperandsOf(list))
    values.push_back(IntegerOf(operand));
  EXPECT_EQ(values, (std::vector<int>{2, 3, 4}));
  vpiHandle one = vpi_handle(vpiDelay, Prim("top", "t"));
  ASSERT_NE(one, nullptr);
  EXPECT_EQ(vpi_get(vpiType, one), vpiConstant);
  EXPECT_EQ(IntegerOf(one), 3);
}

TEST_F(PrimitiveRulesOfARun, APrimitiveWrittenWithNoDelayReachesNone) {
  Run(std::string(kInvUdp) + kArrays);
  for (const char* name : {"g1", "m1", "u1"}) {
    vpiHandle prim = Prim("top", name);
    ASSERT_NE(prim, nullptr) << name;
    EXPECT_EQ(vpi_handle(vpiDelay, prim), nullptr) << name;
  }
}

}  // namespace
}  // namespace delta
