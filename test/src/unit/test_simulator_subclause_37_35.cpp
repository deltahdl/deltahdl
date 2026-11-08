#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "fixture_vpi_run.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_primitive_value.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class PrimitivePrimTerm : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
};

TEST_F(PrimitivePrimTerm, SizeReportsNumberOfInputs) {
  VpiObject prim;
  prim.type = vpiPrimitive;
  prim.size = 3;
  EXPECT_EQ(vpi_get(vpiSize, VpiHandleOf(&prim)), 3);

  VpiObject gate;
  gate.type = vpiGate;
  gate.size = 2;
  EXPECT_EQ(vpi_get(vpiSize, VpiHandleOf(&gate)), 2);
}

TEST_F(PrimitivePrimTerm, TermIndexReportsTerminalOrder) {
  VpiObject first;
  first.type = vpiPrimTerm;
  first.index = 0;
  VpiObject second;
  second.type = vpiPrimTerm;
  second.index = 1;
  VpiObject third;
  third.type = vpiPrimTerm;
  third.index = 2;

  EXPECT_EQ(vpi_get(vpiTermIndex, VpiHandleOf(&first)), 0);
  EXPECT_EQ(vpi_get(vpiTermIndex, VpiHandleOf(&second)), 1);
  EXPECT_EQ(vpi_get(vpiTermIndex, VpiHandleOf(&third)), 2);
}

TEST_F(PrimitivePrimTerm, IndexTransitionReachesArrayIndex) {
  VpiObject index_expr;
  index_expr.type = vpiConstant;

  VpiObject member;
  member.type = vpiPrimitive;
  member.array_member = true;
  member.index_expr = &index_expr;

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiIndex, VpiHandleOf(&member))),
            &index_expr);
}

TEST_F(PrimitivePrimTerm, IndexTransitionIsNullWhenNotAnArrayElement) {
  VpiObject stray_expr;
  stray_expr.type = vpiConstant;

  VpiObject standalone;
  standalone.type = vpiPrimitive;
  standalone.array_member = false;
  standalone.index_expr = &stray_expr;
  standalone.children.push_back(&stray_expr);

  EXPECT_EQ(vpi_handle(vpiIndex, VpiHandleOf(&standalone)), nullptr);
}

TEST_F(PrimitivePrimTerm, AValueIsThatOfTheDrivenTermsExpression) {
  VpiObject a;
  a.type = vpiNet;
  VpiObject y;
  y.type = vpiNet;
  VpiObject in;
  in.type = vpiPrimTerm;
  in.direction = vpiInput;
  in.children.push_back(&a);
  VpiObject other;
  other.type = vpiConstant;
  VpiObject out;
  out.type = vpiPrimTerm;
  out.direction = vpiOutput;
  out.children.push_back(&y);
  VpiObject gate;
  gate.type = vpiGate;
  gate.children = {&in, &other, &out};
  EXPECT_EQ(VpiPrimitiveValueSource(&gate), &y);
  EXPECT_EQ(VpiPrimitiveValueSource(&in), &a);

  VpiObject unconnected;
  unconnected.type = vpiPrimTerm;
  unconnected.direction = vpiInput;
  EXPECT_EQ(VpiPrimitiveValueSource(&unconnected), nullptr);
}

TEST_F(PrimitivePrimTerm, PutValueRejectedOnNonSequentialPrimitive) {
  const int kKinds[] = {vpiGate, vpiSwitch, vpiUdp, vpiPrimitive};
  for (int kind : kKinds) {
    VpiObject prim;
    prim.type = kind;
    prim.prim_type = vpiCombPrim;

    s_vpi_value val = {};
    val.format = vpiScalarVal;
    val.value.scalar = vpi1;
    vpiHandle ret =
        vpi_put_value(VpiHandleOf(&prim), &val, nullptr, vpiNoDelay);
    EXPECT_EQ(ret, nullptr) << "kind " << kind;

    s_vpi_error_info info = {};
    EXPECT_EQ(vpi_chk_error(&info), vpiError) << "kind " << kind;
  }
}

TEST_F(PrimitivePrimTerm, PutValueAcceptedOnSequentialUdp) {
  auto* var = sim_ctx_.CreateVariable("seq", 1);
  var->value = MakeLogic4VecVal(arena_, 1, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("seq"), nullptr);
  ASSERT_NE(h, nullptr);
  VpiObjectOf(h)->type = vpiUdp;
  VpiObjectOf(h)->prim_type = vpiSeqPrim;

  s_vpi_value val = {};
  val.format = vpiScalarVal;
  val.value.scalar = vpi1;
  vpi_put_value(h, &val, nullptr, vpiNoDelay);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), 0);
  EXPECT_EQ(var->value.words[0].aval & 1, 1u);
}

TEST_F(PrimitivePrimTerm, ThePrimitiveClassGroupsTheConcreteKinds) {
  EXPECT_TRUE(VpiIsPrimitiveType(vpiGate));
  EXPECT_TRUE(VpiIsPrimitiveType(vpiSwitch));
  EXPECT_TRUE(VpiIsPrimitiveType(vpiUdp));

  EXPECT_FALSE(VpiIsPrimitiveType(vpiPrimitive));
  EXPECT_FALSE(VpiIsPrimitiveType(kVpiNet));
  EXPECT_FALSE(VpiIsPrimitiveType(vpiIterator));
  EXPECT_FALSE(VpiIsPrimitiveType(vpiIODecl));
}

TEST_F(PrimitivePrimTerm, AModuleIteratesThePrimitivesItInstantiates) {
  VpiObject gate;
  gate.type = vpiGate;
  VpiObject net;
  net.type = kVpiNet;
  VpiObject switch_prim;
  switch_prim.type = vpiSwitch;
  VpiObject udp;
  udp.type = vpiUdp;

  VpiObject mod;
  mod.type = kVpiModule;
  mod.children = {&gate, &net, &switch_prim, &udp};

  vpiHandle it = vpi_iterate(vpiPrimitive, VpiHandleOf(&mod));
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), &gate);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), &switch_prim);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), &udp);
  EXPECT_EQ(vpi_scan(it), nullptr);
}

TEST_F(PrimitivePrimTerm, APrimTermReachesThePrimitiveItBelongsTo) {
  VpiObject udp;
  udp.type = vpiUdp;

  VpiObject term;
  term.type = vpiPrimTerm;
  term.parent = &udp;
  udp.children.push_back(&term);

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiPrimitive, VpiHandleOf(&term))), &udp);
}

TEST_F(PrimitivePrimTerm, AnObjectWithNoPrimitiveReachesNone) {
  VpiObject net;
  net.type = kVpiNet;

  VpiObject mod;
  mod.type = kVpiModule;
  mod.children = {&net};

  EXPECT_EQ(vpi_handle(vpiPrimitive, VpiHandleOf(&mod)), nullptr);
  EXPECT_EQ(vpi_iterate(vpiPrimitive, VpiHandleOf(&mod)), nullptr);
}

TEST_F(PrimitivePrimTerm, ExprPassesOverAChildOfNoExpressionKind) {
  VpiObject attribute;
  attribute.type = vpiAttribute;
  VpiObject term;
  term.type = vpiPrimTerm;
  term.children = {&attribute};
  EXPECT_EQ(vpi_handle(vpiExpr, VpiHandleOf(&term)), nullptr);
}

class PrimitivesOfARun : public VpiDesignRun {
 protected:
  static std::vector<vpiHandle> TermsOf(vpiHandle prim) {
    std::vector<vpiHandle> terms;
    vpiHandle it = vpi_iterate(vpiPrimTerm, prim);
    while (vpiHandle term = it == nullptr ? nullptr : vpi_scan(it)) {
      terms.push_back(term);
    }
    return terms;
  }

  static vpiHandle SecondTerminalExprOfG() {
    vpiHandle g = Named(vpiPrimitive, By("top"), "g");
    const std::vector<vpiHandle> kTerms = TermsOf(g);
    return kTerms.size() < 2 ? nullptr : vpi_handle(vpiExpr, kTerms[1]);
  }
};

constexpr const char* kPrimitives =
    "module top; wire y, o, p; logic a, b, i, c;\n"
    "  and g1(y, a, b);\n"
    "  nmos m1(o, i, c);\n"
    "  pullup pu(p);\n"
    "endmodule\n";

TEST_F(PrimitivesOfARun, AnAndGateIsAGateOfTheRun) {
  Run(kPrimitives);
  EXPECT_EQ(KindsOf(vpiPrimitive, By("top")),
            (std::vector<int>{vpiGate, vpiSwitch, vpiGate}));
  vpiHandle g1 = Named(vpiPrimitive, By("top"), "g1");
  ASSERT_NE(g1, nullptr);
  EXPECT_EQ(vpi_get(vpiPrimType, g1), vpiAndPrim);
  EXPECT_EQ(vpi_get(vpiSize, g1), 2);
  const std::vector<vpiHandle> kTerms = TermsOf(g1);
  ASSERT_EQ(kTerms.size(), 3U);
  EXPECT_EQ(vpi_get(vpiTermIndex, kTerms[0]), 0);
  EXPECT_EQ(vpi_get(vpiDirection, kTerms[0]), vpiOutput);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, kTerms[0])),
            VpiObjectOf(By("top.y")));
  EXPECT_EQ(vpi_get(vpiTermIndex, kTerms[2]), 2);
  EXPECT_EQ(vpi_get(vpiDirection, kTerms[2]), vpiInput);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, kTerms[2])),
            VpiObjectOf(By("top.b")));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiPrimitive, kTerms[1])), VpiObjectOf(g1));
}

TEST_F(PrimitivesOfARun, ASwitchAndAPullupHaveTheirShapes) {
  Run(kPrimitives);
  vpiHandle m1 = Named(vpiPrimitive, By("top"), "m1");
  vpiHandle pu = Named(vpiPrimitive, By("top"), "pu");
  ASSERT_NE(m1, nullptr);
  ASSERT_NE(pu, nullptr);
  EXPECT_EQ(vpi_get(vpiType, m1), vpiSwitch);
  EXPECT_EQ(vpi_get(vpiPrimType, m1), vpiNmosPrim);
  EXPECT_EQ(vpi_get(vpiSize, m1), 2);
  EXPECT_EQ(vpi_get(vpiPrimType, pu), vpiPullupPrim);
  EXPECT_EQ(vpi_get(vpiSize, pu), 0);
  const std::vector<vpiHandle> kTerms = TermsOf(pu);
  ASSERT_EQ(kTerms.size(), 1U);
  EXPECT_EQ(vpi_get(vpiDirection, kTerms[0]), vpiOutput);
}

TEST_F(PrimitivesOfARun, AGateOrSwitchIsAnInstanceOfItsKeyword) {
  Run(kPrimitives);
  const struct {
    const char* name;
    const char* def_name;
  } kCases[] = {{"g1", "and"}, {"m1", "nmos"}, {"pu", "pullup"}};
  for (const auto& c : kCases) {
    vpiHandle prim = Named(vpiPrimitive, By("top"), c.name);
    ASSERT_NE(prim, nullptr) << c.name;
    const char* def_name = vpi_get_str(vpiDefName, prim);
    ASSERT_NE(def_name, nullptr) << c.name;
    EXPECT_STREQ(def_name, c.def_name);
  }
}

TEST_F(PrimitivesOfARun, AUdpInstanceIsAUdpOfTheRun) {
  Run("primitive mux_udp(y, s, a, b);\n"
      "  output y;\n"
      "  input s, a, b;\n"
      "  table\n"
      "    0 0 ? : 0;\n"
      "    0 1 ? : 1;\n"
      "    1 ? 0 : 0;\n"
      "    1 ? 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n"
      "module top; wire y; logic s, a, b;\n"
      "  mux_udp u1(y, s, a, b);\n"
      "endmodule\n");
  vpiHandle u1 = Named(vpiPrimitive, By("top"), "u1");
  ASSERT_NE(u1, nullptr);
  EXPECT_EQ(vpi_get(vpiType, u1), vpiUdp);
  EXPECT_EQ(vpi_get(vpiPrimType, u1), vpiCombPrim);
  EXPECT_EQ(vpi_get(vpiSize, u1), 3);
  const char* def_name = vpi_get_str(vpiDefName, u1);
  ASSERT_NE(def_name, nullptr);
  EXPECT_STREQ(def_name, "mux_udp");
  const std::vector<vpiHandle> kTerms = TermsOf(u1);
  ASSERT_EQ(kTerms.size(), 4U);
  EXPECT_EQ(vpi_get(vpiDirection, kTerms[0]), vpiOutput);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, kTerms[0])),
            VpiObjectOf(By("top.y")));
  EXPECT_EQ(vpi_get(vpiDirection, kTerms[3]), vpiInput);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, kTerms[3])),
            VpiObjectOf(By("top.b")));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiPrimitive, kTerms[1])), VpiObjectOf(u1));
  vpiHandle defn = vpi_handle(vpiUdpDefn, u1);
  ASSERT_NE(defn, nullptr);
  EXPECT_EQ(vpi_get(vpiType, defn), vpiUdpDefn);
  EXPECT_STREQ(vpi_get_str(vpiDefName, defn), "mux_udp");
}

TEST_F(PrimitivesOfARun, EveryGateAndSwitchKeywordHasItsShape) {
  Run("module top; wire w, v; logic a, b, c;\n"
      "  and g_and(w, a, b); nand g_nand(w, a, b);\n"
      "  or g_or(w, a, b); nor g_nor(w, a, b);\n"
      "  xor g_xor(w, a, b); xnor g_xnor(w, a, b);\n"
      "  buf g_buf(w, a); not g_not(w, a);\n"
      "  bufif0 g_bufif0(w, a, c); bufif1 g_bufif1(w, a, c);\n"
      "  notif0 g_notif0(w, a, c); notif1 g_notif1(w, a, c);\n"
      "  tran g_tran(w, v); rtran g_rtran(w, v);\n"
      "  tranif0 g_tranif0(w, v, c); tranif1 g_tranif1(w, v, c);\n"
      "  rtranif0 g_rtranif0(w, v, c); rtranif1 g_rtranif1(w, v, c);\n"
      "  nmos g_nmos(w, a, c); pmos g_pmos(w, a, c);\n"
      "  rnmos g_rnmos(w, a, c); rpmos g_rpmos(w, a, c);\n"
      "  cmos g_cmos(w, a, b, c); rcmos g_rcmos(w, a, b, c);\n"
      "  pullup g_pullup(w); pulldown g_pulldown(v);\n"
      "endmodule\n");
  const struct {
    const char* keyword;
    int type;
    int prim_type;
  } kCases[] = {{"and", vpiGate, vpiAndPrim},
                {"nand", vpiGate, vpiNandPrim},
                {"or", vpiGate, vpiOrPrim},
                {"nor", vpiGate, vpiNorPrim},
                {"xor", vpiGate, vpiXorPrim},
                {"xnor", vpiGate, vpiXnorPrim},
                {"buf", vpiGate, vpiBufPrim},
                {"not", vpiGate, vpiNotPrim},
                {"bufif0", vpiGate, vpiBufif0Prim},
                {"bufif1", vpiGate, vpiBufif1Prim},
                {"notif0", vpiGate, vpiNotif0Prim},
                {"notif1", vpiGate, vpiNotif1Prim},
                {"tran", vpiSwitch, vpiTranPrim},
                {"rtran", vpiSwitch, vpiRtranPrim},
                {"tranif0", vpiSwitch, vpiTranif0Prim},
                {"tranif1", vpiSwitch, vpiTranif1Prim},
                {"rtranif0", vpiSwitch, vpiRtranif0Prim},
                {"rtranif1", vpiSwitch, vpiRtranif1Prim},
                {"nmos", vpiSwitch, vpiNmosPrim},
                {"pmos", vpiSwitch, vpiPmosPrim},
                {"rnmos", vpiSwitch, vpiRnmosPrim},
                {"rpmos", vpiSwitch, vpiRpmosPrim},
                {"cmos", vpiSwitch, vpiCmosPrim},
                {"rcmos", vpiSwitch, vpiRcmosPrim},
                {"pullup", vpiGate, vpiPullupPrim},
                {"pulldown", vpiGate, vpiPulldownPrim}};
  for (const auto& c : kCases) {
    const std::string kName = std::string("g_") + c.keyword;
    vpiHandle prim = Named(vpiPrimitive, By("top"), kName.c_str());
    ASSERT_NE(prim, nullptr) << c.keyword;
    EXPECT_EQ(vpi_get(vpiType, prim), c.type) << c.keyword;
    EXPECT_EQ(vpi_get(vpiPrimType, prim), c.prim_type) << c.keyword;
    const char* def_name = vpi_get_str(vpiDefName, prim);
    ASSERT_NE(def_name, nullptr) << c.keyword;
    EXPECT_STREQ(def_name, c.keyword);
  }
}

TEST_F(PrimitivesOfARun, TerminalsRunAsTheirPrimitiveDrivesThem) {
  Run("module top; wire w, v, x; logic a, c;\n"
      "  tranif1 t(w, v, c);\n"
      "  buf b2(w, x, a);\n"
      "  pulldown pd(v);\n"
      "endmodule\n");
  const struct {
    const char* name;
    std::vector<int> directions;
    int inputs;
  } kCases[] = {{"t", {vpiInout, vpiInout, vpiInput}, 1},
                {"b2", {vpiOutput, vpiOutput, vpiInput}, 1},
                {"pd", {vpiOutput}, 0}};
  for (const auto& c : kCases) {
    vpiHandle prim = Named(vpiPrimitive, By("top"), c.name);
    ASSERT_NE(prim, nullptr) << c.name;
    std::vector<int> directions;
    for (vpiHandle term : TermsOf(prim)) {
      directions.push_back(vpi_get(vpiDirection, term));
    }
    EXPECT_EQ(directions, c.directions) << c.name;
    EXPECT_EQ(vpi_get(vpiSize, prim), c.inputs) << c.name;
  }
}

TEST_F(PrimitivesOfARun, AnUnnamedGateIsAPrimitiveOfTheInstance) {
  Run("module top; wire y; logic a, b;\n"
      "  or (y, a, b);\n"
      "endmodule\n");
  vpiHandle it = vpi_iterate(vpiPrimitive, By("top"));
  ASSERT_NE(it, nullptr);
  vpiHandle prim = vpi_scan(it);
  ASSERT_NE(prim, nullptr);
  EXPECT_EQ(vpi_get(vpiPrimType, prim), vpiOrPrim);
  EXPECT_EQ(TermsOf(prim).size(), 3U);
}

TEST_F(PrimitivesOfARun, ASequentialUdpInstanceReportsVpiSeqPrim) {
  Run("primitive latch_udp(q, d, en);\n"
      "  output reg q;\n"
      "  input d, en;\n"
      "  table\n"
      "    0 1 : ? : 0;\n"
      "    1 1 : ? : 1;\n"
      "    ? 0 : ? : -;\n"
      "  endtable\n"
      "endprimitive\n"
      "module top; wire q; logic d, en;\n"
      "  latch_udp u1(q, d, en);\n"
      "endmodule\n");
  vpiHandle u1 = Named(vpiPrimitive, By("top"), "u1");
  ASSERT_NE(u1, nullptr);
  EXPECT_EQ(vpi_get(vpiPrimType, u1), vpiSeqPrim);
}

TEST_F(PrimitivesOfARun, ATerminalSelectingAStructMemberReachesTheMember) {
  Run("module top; struct {logic a; logic b;} s; wire y; logic c;\n"
      "  and g(y, s.a, c);\n"
      "endmodule\n");
  vpiHandle member = By("top.s.a");
  ASSERT_NE(member, nullptr);
  EXPECT_EQ(VpiObjectOf(SecondTerminalExprOfG()), VpiObjectOf(member));
}

TEST_F(PrimitivesOfARun, ATerminalSelectingAnArrayElementReachesTheElement) {
  Run("module top; logic v [2]; wire y; logic c;\n"
      "  and g(y, v[1], c);\n"
      "endmodule\n");
  vpiHandle element = By("top.v[1]");
  ASSERT_NE(element, nullptr);
  EXPECT_EQ(VpiObjectOf(SecondTerminalExprOfG()), VpiObjectOf(element));
}

TEST_F(PrimitivesOfARun, TerminalsSelectingNoModelledElementAreKept) {
  Run("module top; wire w [2]; logic u [2]; int i; wire y, z; logic c;\n"
      "  and g(y, w[i], c);\n"
      "  and h(z, u[5], c);\n"
      "endmodule\n");
  for (const char* name : {"g", "h"}) {
    vpiHandle gate = Named(vpiPrimitive, By("top"), name);
    ASSERT_NE(gate, nullptr) << name;
    const std::vector<vpiHandle> kTerms = TermsOf(gate);
    ASSERT_EQ(kTerms.size(), 3U) << name;
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, kTerms[2])),
              VpiObjectOf(By("top.c")))
        << name;
  }
}

TEST_F(PrimitivePrimTerm, PrimitiveIsTheParentOrElseAHeldPrimitive) {
  VpiObject module;
  module.type = vpiModule;
  VpiObject gate;
  gate.type = vpiGate;
  VpiObject holder;
  holder.type = vpiPrimTerm;
  holder.parent = &module;
  holder.children = {&gate};
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiPrimitive, VpiHandleOf(&holder))), &gate);
}

int IntValueOf(vpiHandle obj) {
  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = -1;
  vpi_get_value(obj, &value);
  return value.value.integer;
}

TEST_F(PrimitivesOfARun, AGateAndItsTermsReadTheirValues) {
  Run("module top; wire y; logic a = 1, b = 0;\n"
      "  and g(y, a, b);\n"
      "endmodule\n");
  vpiHandle g = Named(vpiPrimitive, By("top"), "g");
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(IntValueOf(g), 0);
  const std::vector<vpiHandle> kTerms = TermsOf(g);
  ASSERT_EQ(kTerms.size(), 3U);
  EXPECT_EQ(IntValueOf(kTerms[0]), 0);
  EXPECT_EQ(IntValueOf(kTerms[1]), 1);
  EXPECT_EQ(IntValueOf(kTerms[2]), 0);
}

std::vector<PLI_UINT32> DelaysOf(vpiHandle prim, int count) {
  std::vector<s_vpi_time> da(static_cast<std::size_t>(count));
  s_vpi_delay delay = {};
  delay.da = da.data();
  delay.no_of_delays = count;
  delay.time_type = vpiSimTime;
  vpi_get_delays(prim, &delay);
  std::vector<PLI_UINT32> ticks;
  ticks.reserve(da.size());
  for (const s_vpi_time& time : da) ticks.push_back(time.low);
  return ticks;
}

TEST_F(PrimitivesOfARun, APrimitiveReportsItsWrittenDelays) {
  Run("primitive inv_udp(o, a);\n"
      "  output o; input a;\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module top; timeunit 1ns; timeprecision 1ns;\n"
      "  wire y, z, w; logic a;\n"
      "  and #(3, 5) g(y, a, a);\n"
      "  bufif1 #(2, 4, 6) h(z, a, a);\n"
      "  inv_udp #7 u(w, a);\n"
      "  and n(y, a, a);\n"
      "endmodule\n");
  EXPECT_EQ(DelaysOf(Named(vpiPrimitive, By("top"), "g"), 3),
            (std::vector<PLI_UINT32>{3, 5, 3}));
  EXPECT_EQ(DelaysOf(Named(vpiPrimitive, By("top"), "h"), 3),
            (std::vector<PLI_UINT32>{2, 4, 6}));
  EXPECT_EQ(DelaysOf(Named(vpiPrimitive, By("top"), "u"), 2),
            (std::vector<PLI_UINT32>{7, 7}));
  EXPECT_EQ(DelaysOf(Named(vpiPrimitive, By("top"), "n"), 2),
            (std::vector<PLI_UINT32>{0, 0}));
}

TEST_F(PrimitivesOfARun, AnArrayElementReportsTheArraysDelays) {
  Run("module top; timeunit 1ns; timeprecision 1ns;\n"
      "  wire [1:0] y; logic [1:0] a;\n"
      "  not #(4, 6) g[1:0] (y, a);\n"
      "endmodule\n");
  EXPECT_EQ(DelaysOf(Named(vpiPrimitive, By("top"), "g[0]"), 3),
            (std::vector<PLI_UINT32>{4, 6, 4}));
}

class SequentialUdpPuts : public PrimitivesOfARun {
 protected:
  void SetUp() override {
    PrimitivesOfARun::SetUp();
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText("$put_one");
    data.calltf = &PutOneCalltf;
    ASSERT_NE(vpi_register_systf(&data), nullptr);
  }

  static vpiHandle Latch() { return Named(vpiPrimitive, By("top"), "u1"); }

  static PLI_INT32 PutOneCalltf(PLI_BYTE8*) {
    s_vpi_value value = {};
    value.format = vpiScalarVal;
    value.value.scalar = vpi1;
    vpi_put_value(Latch(), &value, nullptr, vpiNoDelay);
    return 0;
  }
};

TEST_F(SequentialUdpPuts, APutBecomesTheUdpsState) {
  Run("primitive latch_udp(q, d, en);\n"
      "  output reg q; input d, en;\n"
      "  initial q = 0;\n"
      "  table\n"
      "    0 1 : ? : 0;\n"
      "    1 1 : ? : 1;\n"
      "    ? 0 : ? : -;\n"
      "  endtable\n"
      "endprimitive\n"
      "module top; wire q; logic d = 0, en = 0;\n"
      "  latch_udp u1(q, d, en);\n"
      "  initial begin #5 $put_one; #1 d = 1; #1 d = 0; end\n"
      "endmodule\n");
  vpiHandle u1 = Latch();
  ASSERT_NE(u1, nullptr);
  EXPECT_EQ(IntValueOf(By("top.q")), 1);
  EXPECT_EQ(IntValueOf(u1), 1);

  s_vpi_value zero = {};
  zero.format = vpiScalarVal;
  zero.value.scalar = vpi0;
  s_vpi_time later = {};
  later.type = vpiSimTime;
  later.low = 2;
  vpi_put_value(u1, &zero, &later, vpiTransportDelay);
  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
  EXPECT_EQ(IntValueOf(By("top.q")), 1);

  s_vpi_value none = {};
  none.format = vpiObjTypeVal;
  vpi_put_value(u1, &none, nullptr, vpiNoDelay);
  EXPECT_EQ(IntValueOf(By("top.q")), 1);

  vpi_put_value(u1, &zero, nullptr, vpiNoDelay);
  EXPECT_EQ(IntValueOf(By("top.q")), 0);

  s_vpi_value unknown = {};
  unknown.format = vpiScalarVal;
  unknown.value.scalar = vpiX;
  vpi_put_value(u1, &unknown, nullptr, vpiNoDelay);
  vpi_put_value(u1, nullptr, nullptr, vpiNoDelay);
  s_vpi_value q = {};
  q.format = vpiScalarVal;
  vpi_get_value(By("top.q"), &q);
  EXPECT_EQ(q.value.scalar, vpiX);
}

TEST_F(SequentialUdpPuts, APutBecomesAnArrayElementsState) {
  Run("primitive latch_udp(q, d, en);\n"
      "  output reg q; input d, en;\n"
      "  initial q = 0;\n"
      "  table\n"
      "    0 1 : ? : 0;\n"
      "    1 1 : ? : 1;\n"
      "    ? 0 : ? : -;\n"
      "  endtable\n"
      "endprimitive\n"
      "module top; wire [1:0] q; logic [1:0] d = 0, en = 0;\n"
      "  latch_udp u[1:0] (q, d, en);\n"
      "endmodule\n");
  vpiHandle u0 = Named(vpiPrimitive, By("top"), "u[0]");
  ASSERT_NE(u0, nullptr);
  s_vpi_value one = {};
  one.format = vpiScalarVal;
  one.value.scalar = vpi1;
  vpi_put_value(u0, &one, nullptr, vpiNoDelay);
  EXPECT_EQ(IntValueOf(By("top.q")), 1);
}

TEST_F(PrimitivesOfARun, AModulesIoDeclsAreNoPrimitives) {
  Run("module top(input a, output y);\n"
      "  and g(y, a, a);\n"
      "endmodule\n");
  EXPECT_EQ(KindsOf(vpiPrimitive, By("top")), (std::vector<int>{vpiGate}));
}
}  // namespace
}  // namespace delta
