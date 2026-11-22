#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

TEST(DynamicPrefixSources, DISABLED_EveryTfCallKindIsAPrefixSource) {
  for (int kind :
       {vpiMethodFuncCall, vpiMethodTaskCall, vpiFuncCall, vpiTaskCall}) {
    EXPECT_TRUE(VpiIsDynamicPrefixSourceType(kind)) << kind;
  }
}

class PrefixesEverywhere : public VpiDesignRun {
 protected:
  static void Walk(vpiHandle stmt, std::vector<vpiHandle>& out, int depth) {
    if (stmt == nullptr || depth > 8) return;
    out.push_back(stmt);
    Walk(vpi_handle(vpiStmt, stmt), out, depth + 1);
    for (vpiHandle inner : ObjectsOf(vpiStmt, stmt)) {
      Walk(inner, out, depth + 1);
    }
  }

  static std::vector<vpiHandle> StatementsOf(vpiHandle scope) {
    std::vector<vpiHandle> stmts;
    if (scope == nullptr) return stmts;
    for (vpiHandle proc : ObjectsOf(vpiProcess, scope)) {
      Walk(vpi_handle(vpiStmt, proc), stmts, 0);
    }
    for (vpiHandle routine : ObjectsOf(vpiTaskFunc, scope)) {
      Walk(vpi_handle(vpiStmt, routine), stmts, 0);
    }
    for (vpiHandle routine : ObjectsOf(vpiMethods, scope)) {
      Walk(vpi_handle(vpiStmt, routine), stmts, 0);
    }
    return stmts;
  }

  static std::string NameOf(vpiHandle obj) {
    const char* name = obj == nullptr ? nullptr : vpi_get_str(vpiName, obj);
    return name == nullptr ? "" : name;
  }

  static vpiHandle RhsOf(vpiHandle scope, const std::string& lhs) {
    for (vpiHandle stmt : StatementsOf(scope)) {
      if (vpi_get(vpiType, stmt) == vpiAssignment &&
          NameOf(vpi_handle(vpiLhs, stmt)) == lhs) {
        return vpi_handle(vpiRhs, stmt);
      }
    }
    return nullptr;
  }

  static std::vector<vpiHandle> OfType(vpiHandle scope, int type) {
    std::vector<vpiHandle> found;
    for (vpiHandle stmt : StatementsOf(scope)) {
      if (vpi_get(vpiType, stmt) == type) found.push_back(stmt);
    }
    return found;
  }

  static std::vector<vpiHandle> TriggeredEvents(vpiHandle scope) {
    std::vector<vpiHandle> events;
    for (vpiHandle stmt : OfType(scope, vpiEventStmt)) {
      events.push_back(vpi_handle(vpiNamedEvent, stmt));
    }
    return events;
  }

  static void ExpectPrefix(vpiHandle obj, int type, int holder,
                           const char* prefix_name) {
    ASSERT_NE(obj, nullptr) << prefix_name;
    EXPECT_EQ(vpi_get(vpiType, obj), type) << prefix_name;
    vpiHandle prefix = vpi_handle(vpiPrefix, obj);
    ASSERT_NE(prefix, nullptr) << prefix_name;
    EXPECT_EQ(vpi_get(vpiType, prefix), holder) << prefix_name;
    EXPECT_EQ(NameOf(prefix), prefix_name);
  }
};

constexpr const char* kSelectsThroughPrefixes =
    "interface ifc; logic [7:0] a; endinterface\n"
    "class C; logic [7:0] v; int arr [0:3]; endclass\n"
    "module top; logic clk; logic [7:0] d; ifc i0();\n"
    "  virtual ifc vif = i0; C c = new;\n"
    "  clocking cb @(posedge clk); input d; endclocking\n"
    "  logic y1, y2, y3; logic [3:0] p1, p2, p3, q1, q2, q3; int y4;\n"
    "  initial begin\n"
    "    y1 = vif.a[1]; y4 = c.arr[1]; y3 = cb.d[0];\n"
    "    p1 = vif.a[3:0]; p2 = c.v[3:0]; p3 = cb.d[3:0];\n"
    "    q1 = vif.a[0+:4]; q2 = c.v[0+:4]; q3 = cb.d[0+:4];\n"
    "  end\n"
    "endmodule\n";

TEST_F(PrefixesEverywhere, DISABLED_ABitSelectThroughEachPrefixReachesIt) {
  Run(kSelectsThroughPrefixes);
  vpiHandle top = By("top");
  ExpectPrefix(RhsOf(top, "y1"), vpiBitSelect, vpiVirtualInterfaceVar, "vif");
  ExpectPrefix(RhsOf(top, "y4"), vpiBitSelect, vpiClassVar, "c");
  ExpectPrefix(RhsOf(top, "y3"), vpiBitSelect, vpiClockingBlock, "cb");
}

TEST_F(PrefixesEverywhere, DISABLED_APartSelectThroughEachPrefixReachesIt) {
  Run(kSelectsThroughPrefixes);
  vpiHandle top = By("top");
  ExpectPrefix(RhsOf(top, "p1"), vpiPartSelect, vpiVirtualInterfaceVar, "vif");
  ExpectPrefix(RhsOf(top, "p2"), vpiPartSelect, vpiClassVar, "c");
  ExpectPrefix(RhsOf(top, "p3"), vpiPartSelect, vpiClockingBlock, "cb");
}

TEST_F(PrefixesEverywhere,
       DISABLED_AnIndexedPartSelectThroughEachPrefixReachesIt) {
  Run(kSelectsThroughPrefixes);
  vpiHandle top = By("top");
  ExpectPrefix(RhsOf(top, "q1"), vpiIndexedPartSelect, vpiVirtualInterfaceVar,
               "vif");
  ExpectPrefix(RhsOf(top, "q2"), vpiIndexedPartSelect, vpiClassVar, "c");
  ExpectPrefix(RhsOf(top, "q3"), vpiIndexedPartSelect, vpiClockingBlock, "cb");
}

constexpr const char* kEventsThroughPrefixes =
    "interface ifc; event e; event ea [0:1]; endinterface\n"
    "class C; event e; event ea [0:1]; endclass\n"
    "module top; ifc i0(); virtual ifc vif = i0; C c = new;\n"
    "  initial begin -> vif.e; -> c.e; -> vif.ea[1]; -> c.ea[1]; end\n"
    "endmodule\n";

TEST_F(PrefixesEverywhere, DISABLED_ANamedEventThroughAPrefixReachesIt) {
  Run(kEventsThroughPrefixes);
  const std::vector<vpiHandle> kEvents = TriggeredEvents(By("top"));
  ASSERT_EQ(kEvents.size(), 4U);
  ExpectPrefix(kEvents[0], vpiNamedEvent, vpiVirtualInterfaceVar, "vif");
  ExpectPrefix(kEvents[1], vpiNamedEvent, vpiClassVar, "c");
}

TEST_F(PrefixesEverywhere,
       DISABLED_ANamedEventArrayElementThroughAPrefixReachesIt) {
  Run(kEventsThroughPrefixes);
  const std::vector<vpiHandle> kEvents = TriggeredEvents(By("top"));
  ASSERT_EQ(kEvents.size(), 4U);
  for (size_t n : {2U, 3U}) {
    vpiHandle element = kEvents[n];
    ASSERT_NE(element, nullptr) << n;
    vpiHandle prefix = vpi_handle(vpiPrefix, element);
    ASSERT_NE(prefix, nullptr) << n;
    EXPECT_EQ(vpi_get(vpiType, prefix),
              n == 2U ? vpiVirtualInterfaceVar : vpiClassVar);
  }
}

constexpr const char* kCallsThroughVif =
    "interface ifc; task t; endtask function int f; return 1; endfunction\n"
    "endinterface\n"
    "class H; virtual ifc vif; endclass\n"
    "module top; ifc i0(); virtual ifc v = i0; H h = new; int y;\n"
    "  initial begin h.vif = i0; v.t(); h.vif.t(); y = v.f(); end\n"
    "endmodule\n";

TEST_F(PrefixesEverywhere, DISABLED_ACallThroughAVirtualInterfaceReachesIt) {
  Run(kCallsThroughVif);
  vpiHandle top = By("top");
  const std::vector<vpiHandle> kTasks = OfType(top, vpiTaskCall);
  ASSERT_EQ(kTasks.size(), 2U);
  ExpectPrefix(kTasks[0], vpiTaskCall, vpiVirtualInterfaceVar, "v");
  ExpectPrefix(kTasks[1], vpiTaskCall, vpiVirtualInterfaceVar, "vif");
  ExpectPrefix(RhsOf(top, "y"), vpiFuncCall, vpiVirtualInterfaceVar, "v");
}

TEST_F(PrefixesEverywhere, DISABLED_AChainsInnermostPrefixIsReached) {
  Run("interface ifc; logic a; endinterface\n"
      "class C; int x; endclass\n"
      "class H; C c = new; virtual ifc vif; endclass\n"
      "module top; ifc i0(); H h = new; int y; logic z;\n"
      "  initial begin h.vif = i0; y = h.c.x; z = h.vif.a; end\n"
      "endmodule\n");
  vpiHandle top = By("top");
  ExpectPrefix(RhsOf(top, "y"), vpiRefObj, vpiClassVar, "c");
  ExpectPrefix(RhsOf(top, "z"), vpiRefObj, vpiVirtualInterfaceVar, "vif");
}

constexpr const char* kPrefixedInEachPlace =
    "interface ifc; logic a; endinterface\n"
    "class C; int x; endclass\n"
    "package pk; function int pf(C c); return c.x; endfunction endpackage\n"
    "interface host; C c = new; int y; initial y = c.x; endinterface\n"
    "program prg; C c = new; int y; initial y = c.x; endprogram\n"
    "class K; C c = new; int y; task kt; y = c.x; endtask endclass\n"
    "module top; host h0(); prg p0();\n"
    "  if (1) begin : g C c = new; int y; initial y = c.x; end\n"
    "endmodule\n";

TEST_F(PrefixesEverywhere, APrefixedExpressionInAnInterfaceOrProgram) {
  Run(kPrefixedInEachPlace);
  ExpectPrefix(RhsOf(By("top.h0"), "y"), vpiRefObj, vpiClassVar, "c");
  ExpectPrefix(RhsOf(By("top.p0"), "y"), vpiRefObj, vpiClassVar, "c");
}

TEST_F(PrefixesEverywhere, APrefixedExpressionInAGenerateBlock) {
  Run(kPrefixedInEachPlace);
  ExpectPrefix(RhsOf(By("top.g"), "y"), vpiRefObj, vpiClassVar, "c");
}

TEST_F(PrefixesEverywhere, APrefixedExpressionInAClassMethod) {
  Run(kPrefixedInEachPlace);
  ExpectPrefix(RhsOf(Named(vpiClassDefn, By("$unit"), "K"), "y"), vpiRefObj,
               vpiClassVar, "c");
}

TEST_F(PrefixesEverywhere, APrefixedExpressionInAPackageFunction) {
  Run(kPrefixedInEachPlace);
  vpiHandle pf = Named(vpiFunction, By("pk"), "pf");
  ASSERT_NE(pf, nullptr);
  vpiHandle ret = nullptr;
  std::vector<vpiHandle> stmts;
  Walk(vpi_handle(vpiStmt, pf), stmts, 0);
  for (vpiHandle stmt : stmts) {
    if (vpi_get(vpiType, stmt) == vpiReturnStmt) {
      ret = vpi_handle(vpiCondition, stmt);
    }
  }
  ExpectPrefix(ret, vpiRefObj, vpiClassVar, "c");
}

TEST_F(PrefixesEverywhere, EachFormOfVirtualInterfaceActsAsAPrefix) {
  Run("interface ifc; logic a; modport mp(input a); endinterface\n"
      "typedef virtual ifc vt;\n"
      "module top; ifc i0(); virtual ifc.mp vm = i0; vt vd = i0;\n"
      "  logic y1, y2, y3;\n"
      "  task tk(virtual ifc va); y3 = va.a; endtask\n"
      "  initial begin y1 = vm.a; y2 = vd.a; tk(i0); end\n"
      "endmodule\n");
  vpiHandle top = By("top");
  ExpectPrefix(RhsOf(top, "y1"), vpiRefObj, vpiVirtualInterfaceVar, "vm");
  ExpectPrefix(RhsOf(top, "y2"), vpiRefObj, vpiVirtualInterfaceVar, "vd");
  ExpectPrefix(RhsOf(top, "y3"), vpiRefObj, vpiVirtualInterfaceVar, "va");
}

TEST_F(PrefixesEverywhere, DISABLED_ATfCallsHasActualFollowsItsPrefix) {
  Run("interface ifc; task t; endtask endinterface\n"
      "class C; task m; endtask endclass\n"
      "module top; ifc i0(); virtual ifc v = i0; C c = new;\n"
      "  initial begin c.m(); v.t(); end\n"
      "endmodule\n");
  vpiHandle top = By("top");
  for (int kind : {vpiMethodTaskCall, vpiTaskCall}) {
    const std::vector<vpiHandle> kCalls = OfType(top, kind);
    ASSERT_EQ(kCalls.size(), 1U) << kind;
    EXPECT_EQ(vpi_get(vpiHasActual, kCalls[0]), 1) << kind;
  }
}

TEST_F(PrefixesEverywhere, DISABLED_AMemberThroughAClassVarHasAnActual) {
  Run("class C; int x; endclass\n"
      "module top; C c = new; C n; int y, z;\n"
      "  initial begin y = c.x; z = n.x; end\n"
      "endmodule\n");
  vpiHandle top = By("top");
  vpiHandle through_object = RhsOf(top, "y");
  vpiHandle through_null = RhsOf(top, "z");
  ASSERT_NE(through_object, nullptr);
  ASSERT_NE(through_null, nullptr);
  EXPECT_EQ(vpi_get(vpiHasActual, through_object), 1);
  EXPECT_EQ(vpi_get(vpiHasActual, through_null), 0);
}

TEST_F(PrefixesEverywhere, DISABLED_AnObjectThroughAClockingBlockHasAnActual) {
  Run("module top; logic clk, d, y;\n"
      "  clocking cb @(posedge clk); input d; endclocking\n"
      "  initial y = cb.d;\n"
      "endmodule\n");
  vpiHandle ref = RhsOf(By("top"), "y");
  ASSERT_NE(ref, nullptr);
  EXPECT_EQ(vpi_get(vpiHasActual, ref), 1);
}

TEST_F(PrefixesEverywhere, StaticSelectsAndEventArraysHaveAnActual) {
  Run("module top; logic [7:0] v; event ea [0:1]; logic [3:0] p, q;\n"
      "  initial begin p = v[3:0]; q = v[0+:4]; end\n"
      "endmodule\n");
  vpiHandle top = By("top");
  for (const char* lhs : {"p", "q"}) {
    vpiHandle select = RhsOf(top, lhs);
    ASSERT_NE(select, nullptr) << lhs;
    EXPECT_EQ(vpi_get(vpiHasActual, select), 1) << lhs;
  }
  vpiHandle events = Named(vpiNamedEventArray, top, "ea");
  ASSERT_NE(events, nullptr);
  EXPECT_EQ(vpi_get(vpiHasActual, events), 1);
}

TEST_F(PrefixesEverywhere, LexicalVariablesHaveNoActual) {
  Run("class C; int x; endclass\n"
      "module top; C c = new;\n"
      "  task automatic tk; int a; a = 1; endtask\n"
      "endmodule\n");
  vpiHandle top = By("top");
  vpiHandle defn_var =
      Named(vpiVariables, Named(vpiClassDefn, By("$unit"), "C"), "x");
  ASSERT_NE(defn_var, nullptr);
  EXPECT_EQ(vpi_get(vpiHasActual, defn_var), 0);
  vpiHandle typespec =
      vpi_handle(vpiClassTypespec, vpi_handle(vpiClassObj, By("top.c")));
  vpiHandle typespec_var = Named(vpiVariables, typespec, "x");
  ASSERT_NE(typespec_var, nullptr);
  EXPECT_EQ(vpi_get(vpiHasActual, typespec_var), 0);
  vpiHandle task_var = Named(vpiVariables, Named(vpiTask, top, "tk"), "a");
  ASSERT_NE(task_var, nullptr);
  EXPECT_EQ(vpi_get(vpiHasActual, task_var), 0);
}

std::vector<int> g_frame_actuals;

PLI_INT32 RecordFrameActualsCalltf(PLI_BYTE8*) {
  vpiHandle frame = vpi_handle(vpiFrame, nullptr);
  vpiHandle it = frame == nullptr ? nullptr : vpi_iterate(vpiAutomatics, frame);
  while (vpiHandle obj = it == nullptr ? nullptr : vpi_scan(it)) {
    g_frame_actuals.push_back(vpi_get(vpiHasActual, obj));
  }
  return 0;
}

TEST_F(PrefixesEverywhere, DISABLED_AFramesAutomaticVariableHasAnActual) {
  g_frame_actuals.clear();
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$frameactuals");
  data.calltf = &RecordFrameActualsCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
  Run("module top;\n"
      "  task automatic tk; int a; a = 2; $frameactuals; endtask\n"
      "  initial tk();\n"
      "endmodule\n");
  EXPECT_EQ(g_frame_actuals, (std::vector<int>{1}));
}

constexpr const char* kSchemesOfPrefixes =
    "interface ifc; logic [7:0] a; event e; task t; endtask endinterface\n"
    "class C; int x; logic [7:0] v; event e; task m; endtask endclass\n"
    "module top; ifc i0(); C ms = new; virtual ifc vs = i0;\n"
    "  int y1, y2; logic z1, z2; logic [3:0] p1, p2;\n"
    "  task automatic tk;\n"
    "    C ma = new; virtual ifc va = i0;\n"
    "    y1 = ma.x; z1 = va.a; p1 = ma.v[3:0];\n"
    "    -> ma.e; -> va.e; ma.m(); va.t();\n"
    "  endtask\n"
    "  initial begin\n"
    "    y2 = ms.x; z2 = vs.a; p2 = vs.a[3:0];\n"
    "  end\n"
    "endmodule\n";

TEST_F(PrefixesEverywhere, AMemberThroughAClassVarReportsTheVarsScheme) {
  Run(kSchemesOfPrefixes);
  vpiHandle top = By("top");
  EXPECT_EQ(vpi_get(vpiAllocScheme, RhsOf(top, "y1")), vpiAutomaticScheme);
  EXPECT_EQ(vpi_get(vpiAllocScheme, RhsOf(top, "y2")), vpiOtherScheme);
}

TEST_F(PrefixesEverywhere,
       AMemberThroughAVirtualInterfaceReportsTheVarsScheme) {
  Run(kSchemesOfPrefixes);
  vpiHandle top = By("top");
  EXPECT_EQ(vpi_get(vpiAllocScheme, RhsOf(top, "z1")), vpiAutomaticScheme);
  EXPECT_EQ(vpi_get(vpiAllocScheme, RhsOf(top, "z2")), vpiOtherScheme);
}

TEST_F(PrefixesEverywhere,
       DISABLED_EachPrefixedSourceKindReportsThePrefixsScheme) {
  Run(kSchemesOfPrefixes);
  vpiHandle top = By("top");
  EXPECT_EQ(vpi_get(vpiAllocScheme, RhsOf(top, "p1")), vpiAutomaticScheme);
  EXPECT_EQ(vpi_get(vpiAllocScheme, RhsOf(top, "p2")), vpiOtherScheme);
  for (vpiHandle event : TriggeredEvents(top)) {
    ASSERT_NE(event, nullptr);
    EXPECT_EQ(vpi_get(vpiAllocScheme, event), vpiAutomaticScheme);
  }
  for (int kind : {vpiMethodTaskCall, vpiTaskCall}) {
    const std::vector<vpiHandle> kCalls = OfType(top, kind);
    ASSERT_EQ(kCalls.size(), 1U) << kind;
    EXPECT_EQ(vpi_get(vpiAllocScheme, kCalls[0]), vpiAutomaticScheme) << kind;
  }
}

}  // namespace
}  // namespace delta
