#include <gtest/gtest.h>

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
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// §37.35 Primitive, prim term: the VPI object model for a primitive (gate,
// switch, or UDP) and the prim-term objects that carry its terminals. The
// diagram's property labels (vpiDefName, vpiName/vpiFullName, vpiPrimType,
// vpiStrength0/1, the array-member booleans) and structural edges (to module,
// primitive array, udp defn, the delay expr, and the prim term's
// value/direction) are read by the generic object-model machinery and the
// value/delay routines owned by other subclauses. The four numbered Details
// carry this clause's own rules, and the tests below observe the production
// code that applies them:
//   D1 - vpiSize returns a primitive's number of inputs (the kVpiSize
//   dispatch). D2 - vpi_put_value() is allowed only on a sequential UDP
//   primitive
//        (the guard at the head of PutValue).
//   D3 - vpiTermIndex reports a prim term's terminal order, first index zero
//        (the vpiTermIndex dispatch).
//   D4 - vpiIndex from a primitive reaches its array index, or NULL when the
//        primitive is not an array element (the Handle transition).

// The fixture installs a context so the public vpi_get/vpi_handle/vpi_put_value
// entry points run their real dispatch, and provides the simulation plumbing a
// sequential-UDP value put needs.
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

// D1: vpiSize on a primitive reports its number of inputs. A primitive stores
// that input count as its size, and vpi_get(vpiSize) hands it back through the
// shared size dispatch.
TEST_F(PrimitivePrimTerm, SizeReportsNumberOfInputs) {
  VpiObject prim;
  prim.type = vpiPrimitive;
  prim.size = 3;  // a three-input primitive
  EXPECT_EQ(vpi_get(vpiSize, VpiHandleOf(&prim)), 3);

  VpiObject gate;
  gate.type = vpiGate;
  gate.size = 2;
  EXPECT_EQ(vpi_get(vpiSize, VpiHandleOf(&gate)), 2);
}

// D3: a prim term reports its terminal index through vpiTermIndex, which fixes
// the terminal order. The first terminal carries index zero; successive
// terminals report 1, 2, ... so the order is recoverable.
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

  // The first terminal has term index zero.
  EXPECT_EQ(vpi_get(vpiTermIndex, VpiHandleOf(&first)), 0);
  EXPECT_EQ(vpi_get(vpiTermIndex, VpiHandleOf(&second)), 1);
  EXPECT_EQ(vpi_get(vpiTermIndex, VpiHandleOf(&third)), 2);
}

// D4: vpiIndex from a primitive that is an element of a primitive array reaches
// the index expression that locates it within the array.
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

// D4: for a primitive that is not part of a primitive array, the vpiIndex
// transition returns NULL - even if some other expr is hanging off the object,
// the transition is meaningful only for an array member.
TEST_F(PrimitivePrimTerm, IndexTransitionIsNullWhenNotAnArrayElement) {
  VpiObject stray_expr;
  stray_expr.type = vpiConstant;

  VpiObject standalone;
  standalone.type = vpiPrimitive;
  standalone.array_member = false;
  standalone.index_expr = &stray_expr;  // present but must not be reported
  standalone.children.push_back(&stray_expr);

  EXPECT_EQ(vpi_handle(vpiIndex, VpiHandleOf(&standalone)), nullptr);
}

// D2: vpi_put_value() applied to a primitive that is not a sequential UDP - a
// gate, switch, combinational UDP, or generic primitive - is rejected. The put
// returns NULL and records a vpi_chk_error() error, leaving nothing written.
TEST_F(PrimitivePrimTerm, PutValueRejectedOnNonSequentialPrimitive) {
  const int kKinds[] = {vpiGate, vpiSwitch, vpiUdp, vpiCombPrim, vpiPrimitive};
  for (int kind : kKinds) {
    VpiObject prim;
    prim.type = kind;

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

// D2: the same routine accepts a value put to a sequential UDP - the one
// primitive kind that may be written. The §37.35 restriction does not fire, and
// (with the required vpiNoDelay flag) the value is applied with no error.
TEST_F(PrimitivePrimTerm, PutValueAcceptedOnSequentialUdp) {
  auto* var = sim_ctx_.CreateVariable("seq", 1);
  var->value = MakeLogic4VecVal(arena_, 1, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("seq"), nullptr);
  ASSERT_NE(h, nullptr);
  VpiObjectOf(h)->type = vpiSeqPrim;

  s_vpi_value val = {};
  val.format = vpiScalarVal;
  val.value.scalar = vpi1;
  vpi_put_value(h, &val, nullptr, vpiNoDelay);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), 0);
  EXPECT_EQ(var->value.words[0].aval & 1, 1u);
}

// -----------------------------------------------------------------------------
// The `primitive` class. §37.35 draws it as a class definition - bold italic
// letters in a dotted enclosure - holding the gate, switch and udp object
// definitions, and §37.5 draws the module's edge to that enclosure. §37.4.1
// makes such an enclosure a grouping rather than an object of its own, so
// vpiPrimitive names the group; matching it against an object's own type, which
// is what the generic traversal does, reached no primitive of any design.
// -----------------------------------------------------------------------------

// Class membership: the kinds the enclosure holds are the gate, the switch and
// the udp, the last in the sequential and combinational forms §37.36 detail 2
// distinguishes. The class constant itself is not one of them.
TEST_F(PrimitivePrimTerm, ThePrimitiveClassGroupsTheConcreteKinds) {
  EXPECT_TRUE(VpiIsPrimitiveType(vpiGate));
  EXPECT_TRUE(VpiIsPrimitiveType(vpiSwitch));
  EXPECT_TRUE(VpiIsPrimitiveType(vpiUdp));
  EXPECT_TRUE(VpiIsPrimitiveType(vpiSeqPrim));
  EXPECT_TRUE(VpiIsPrimitiveType(vpiCombPrim));

  EXPECT_FALSE(VpiIsPrimitiveType(vpiPrimitive));
  EXPECT_FALSE(VpiIsPrimitiveType(kVpiNet));
}

// §37.5 (figure, module ==> primitive): a module's primitives are what the edge
// drawn to the class reaches, so the iteration hands back the gate, the switch
// and the UDP the module instantiates. A net of the same module is not one.
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

// §37.35 (figure, primitive <-> prim term): a terminal and the primitive it
// belongs to are drawn to each other, the primitive end being the class. The
// terminal reaches its primitive, whichever of the class's kinds it is.
TEST_F(PrimitivePrimTerm, APrimTermReachesThePrimitiveItBelongsTo) {
  VpiObject udp;
  udp.type = vpiUdp;

  VpiObject term;
  term.type = vpiPrimTerm;
  term.parent = &udp;
  udp.children.push_back(&term);

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiPrimitive, VpiHandleOf(&term))), &udp);
}

// §37.35 (figure): an object standing in no such relationship reaches no
// primitive rather than some object of an unrelated kind.
TEST_F(PrimitivePrimTerm, AnObjectWithNoPrimitiveReachesNone) {
  VpiObject net;
  net.type = kVpiNet;

  VpiObject mod;
  mod.type = kVpiModule;
  mod.children = {&net};

  EXPECT_EQ(vpi_handle(vpiPrimitive, VpiHandleOf(&mod)), nullptr);
  EXPECT_EQ(vpi_iterate(vpiPrimitive, VpiHandleOf(&mod)), nullptr);
}

// The primitives of a run: those a design instantiates, built from the
// elaborated design rather than by hand (#4957).
class PrimitivesOfARun : public VpiDesignRun {
 protected:
  // The terminals of `prim`, in the order written.
  static std::vector<vpiHandle> TermsOf(vpiHandle prim) {
    std::vector<vpiHandle> terms;
    vpiHandle it = vpi_iterate(vpiPrimTerm, prim);
    while (vpiHandle term = it == nullptr ? nullptr : vpi_scan(it)) {
      terms.push_back(term);
    }
    return terms;
  }

  // What the second terminal of top's gate g reaches through vpiExpr; null
  // where top has no such gate.
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

// An and gate is a gate of the instance, reporting its primitive type and its
// number of inputs (detail 1), its terminals in order from index zero
// (detail 3), the output first, each reaching the net or variable it connects
// and the gate it belongs to.
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

// A MOS switch is a switch, its data input and control its two inputs; a
// pullup is a gate with one output and no input.
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

// §37.35 with §38.11: a primitive's definition name is what it is an instance
// of - a gate's or a switch's built-in primitive, named by its keyword. Every
// primitive answered null.
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

// §37.35 with §29.8: an instance of a UDP is a udp of the instance holding it,
// the third kind the primitive class groups. It reports its UDP's primitive
// type, its number of inputs and its UDP's name as its definition name, its
// output terminal first and its inputs after, and reaches the udp defn of its
// UDP (§37.36). No UDP instance had an object, so none of this answered.
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

// §37.35 with Table 28-1 (§28.3): every gate and switch keyword makes a
// primitive of its own kind -- a gate or a switch, with that keyword's
// primitive type and the keyword as its definition name. Only and, nmos and
// pullup were tested, so a wrong entry for any other keyword went unseen.
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

// §37.13 detail 1 read on §37.35's prim terms: a bidirectional switch's two
// channel terminals are inout and its control an input (§28.8); a buf gate
// drives every terminal but its last (§28.5); a pulldown drives its one
// terminal (§28.10). The size counts the inputs (detail 1).
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

// §28.3.4 makes a gate's instance name optional, and an instantiation written
// without one is still a primitive of the instance, of its keyword's type.
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

// §37.35 with §29.5: an instance of a sequential UDP reports vpiSeqPrim, where
// a combinational one reports vpiCombPrim.
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

// §37.35 with §37.17 details 3 and 26: a terminal written as a member of an
// unpacked structure, `s.a`, reaches that member variable. The member access
// was taken for a hierarchical name, and its first name resolving in the
// scope gave no object at all.
TEST_F(PrimitivesOfARun, ATerminalSelectingAStructMemberReachesTheMember) {
  Run("module top; struct {logic a; logic b;} s; wire y; logic c;\n"
      "  and g(y, s.a, c);\n"
      "endmodule\n");
  vpiHandle member = By("top.s.a");
  ASSERT_NE(member, nullptr);
  EXPECT_EQ(VpiObjectOf(SecondTerminalExprOfG()), VpiObjectOf(member));
}

// §37.35 with §37.17 details 2 and 26: a terminal written as an element of an
// unpacked array, `v[1]`, reaches that element. The select looked for a bit
// of the array, which has none, and gave no object.
TEST_F(PrimitivesOfARun, ATerminalSelectingAnArrayElementReachesTheElement) {
  Run("module top; logic v [2]; wire y; logic c;\n"
      "  and g(y, v[1], c);\n"
      "endmodule\n");
  vpiHandle element = By("top.v[1]");
  ASSERT_NE(element, nullptr);
  EXPECT_EQ(VpiObjectOf(SecondTerminalExprOfG()), VpiObjectOf(element));
}

}  // namespace
}  // namespace delta
