#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class CallsInMethodBodies : public VpiDesignRun {
 protected:
  static vpiHandle UnitScope() {
    for (vpiHandle pkg : ObjectsOf(vpiPackage, nullptr)) {
      if (vpi_get(vpiUnit, pkg) == 1) return pkg;
    }
    return nullptr;
  }

  static vpiHandle MethodOf(vpiHandle scope, std::string_view cls,
                            std::string_view method) {
    return Named(vpiMethods, Named(vpiClassDefn, scope, cls), method);
  }

  static std::vector<vpiHandle> CallsIn(vpiHandle tf) {
    std::vector<vpiHandle> calls;
    vpiHandle body = tf == nullptr ? nullptr : vpi_handle(vpiStmt, tf);
    if (body == nullptr) return calls;
    std::vector<vpiHandle> stmts = {body};
    if (vpi_get(vpiType, body) == vpiBegin) stmts = ObjectsOf(vpiStmt, body);
    for (vpiHandle stmt : stmts) {
      const bool kAssigned = vpi_get(vpiType, stmt) == vpiAssignment;
      calls.push_back(kAssigned ? vpi_handle(vpiRhs, stmt) : stmt);
    }
    return calls;
  }

  static std::vector<int> KindsIn(vpiHandle tf) {
    std::vector<int> kinds;
    for (vpiHandle call : CallsIn(tf)) kinds.push_back(vpi_get(vpiType, call));
    return kinds;
  }

  static VpiObject* Reached(int relation, vpiHandle call) {
    vpiHandle reached = call == nullptr ? nullptr : vpi_handle(relation, call);
    return reached == nullptr ? nullptr : VpiObjectOf(reached);
  }

  static VpiObject* Declared(vpiHandle scope, std::string_view name) {
    vpiHandle declared = Named(vpiTaskFunc, scope, name);
    return declared == nullptr ? nullptr : VpiObjectOf(declared);
  }
};

std::string EveryCallKindIn(std::string_view open, std::string_view close) {
  return std::string(open) +
         "  task t; endtask\n"
         "  function int f(); return 1; endfunction\n"
         "  class D; task mt; endtask\n"
         "    function int mf(); return 2; endfunction endclass\n"
         "  class C; int r; D o;\n"
         "    task m; begin\n"
         "      t(); r = f(); o.mt(); r = o.mf(); $display(\"x\");\n"
         "      r = $clog2(4);\n"
         "    end endtask\n"
         "  endclass\n" +
         std::string(close);
}

std::vector<int> EveryCallKind() {
  return {vpiTaskCall,       vpiFuncCall,    vpiMethodTaskCall,
          vpiMethodFuncCall, vpiSysTaskCall, vpiSysFuncCall};
}

TEST_F(CallsInMethodBodies, DISABLED_AModuleClasssMethodHoldsEveryCallKind) {
  Run(EveryCallKindIn("module top;\n", "endmodule\n"));
  EXPECT_EQ(KindsIn(MethodOf(By("top"), "C", "m")), EveryCallKind());
}

TEST_F(CallsInMethodBodies, DISABLED_APackageClasssMethodHoldsEveryCallKind) {
  Run(EveryCallKindIn("package pk;\n", "endpackage\nmodule top; endmodule\n"));
  EXPECT_EQ(KindsIn(MethodOf(By("pk"), "C", "m")), EveryCallKind());
}

TEST_F(CallsInMethodBodies, DISABLED_AUnitClasssMethodHoldsEveryCallKind) {
  Run(EveryCallKindIn("", "module top; endmodule\n"));
  EXPECT_EQ(KindsIn(MethodOf(UnitScope(), "C", "m")), EveryCallKind());
}

TEST_F(CallsInMethodBodies,
       DISABLED_AModuleClasssMethodReachesTheModulesSubroutines) {
  Run(EveryCallKindIn("module top;\n", "endmodule\n"));
  const std::vector<vpiHandle> kCalls = CallsIn(MethodOf(By("top"), "C", "m"));
  ASSERT_EQ(kCalls.size(), EveryCallKind().size());
  ASSERT_NE(Declared(By("top"), "t"), nullptr);
  EXPECT_EQ(Reached(vpiTask, kCalls[0]), Declared(By("top"), "t"));
  ASSERT_NE(Declared(By("top"), "f"), nullptr);
  EXPECT_EQ(Reached(vpiFunction, kCalls[1]), Declared(By("top"), "f"));
}

TEST_F(CallsInMethodBodies,
       DISABLED_ANameTheModuleAndTheClassDeclareIsTheClasss) {
  Run("module top;\n"
      "  function int f(); return 1; endfunction\n"
      "  task t; endtask\n"
      "  class C; int r;\n"
      "    function int f(); return 2; endfunction\n"
      "    task t; endtask\n"
      "    task m; begin r = f(); t(); end endtask\n"
      "  endclass\n"
      "endmodule\n");
  const std::vector<vpiHandle> kCalls = CallsIn(MethodOf(By("top"), "C", "m"));
  ASSERT_EQ(kCalls.size(), 2U);
  vpiHandle f = MethodOf(By("top"), "C", "f");
  vpiHandle t = MethodOf(By("top"), "C", "t");
  ASSERT_NE(f, nullptr);
  ASSERT_NE(t, nullptr);
  EXPECT_EQ(Reached(vpiFunction, kCalls[0]), VpiObjectOf(f));
  EXPECT_EQ(Reached(vpiTask, kCalls[1]), VpiObjectOf(t));
}

constexpr const char* kUnitClassCalls =
    "function int f(); return 1; endfunction\n"
    "function int g(); return 2; endfunction\n"
    "task t; endtask\n"
    "import \"DPI-C\" function int c_f();\n"
    "class C; int r;\n"
    "  function int g(); return 3; endfunction\n"
    "  function void a(); void'(f()); endfunction\n"
    "  task b; t(); endtask\n"
    "  function void c(); r = c_f(); endfunction\n"
    "  extern function void d();\n"
    "  function void e(); r = g(); endfunction\n"
    "endclass\n"
    "function void C::d(); void'(f()); endfunction\n"
    "module top; endmodule\n";

TEST_F(CallsInMethodBodies,
       DISABLED_AUnitClasssFunctionCallReachesTheUnitsFunction) {
  Run(kUnitClassCalls);
  const std::vector<vpiHandle> kCalls =
      CallsIn(MethodOf(UnitScope(), "C", "a"));
  ASSERT_EQ(kCalls.size(), 1U);
  vpiHandle f = vpi_handle(vpiFunction, kCalls[0]);
  ASSERT_NE(f, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, f), "$unit::f");
}

TEST_F(CallsInMethodBodies, DISABLED_AUnitClasssTaskEnableReachesTheUnitsTask) {
  Run(kUnitClassCalls);
  const std::vector<vpiHandle> kCalls =
      CallsIn(MethodOf(UnitScope(), "C", "b"));
  ASSERT_EQ(kCalls.size(), 1U);
  ASSERT_NE(Declared(UnitScope(), "t"), nullptr);
  EXPECT_EQ(Reached(vpiTask, kCalls[0]), Declared(UnitScope(), "t"));
}

TEST_F(CallsInMethodBodies, DISABLED_AUnitClasssDpiCallReachesTheUnitsImport) {
  Run(kUnitClassCalls);
  const std::vector<vpiHandle> kCalls =
      CallsIn(MethodOf(UnitScope(), "C", "c"));
  ASSERT_EQ(kCalls.size(), 1U);
  ASSERT_NE(Declared(UnitScope(), "c_f"), nullptr);
  EXPECT_EQ(Reached(vpiFunction, kCalls[0]), Declared(UnitScope(), "c_f"));
}

TEST_F(CallsInMethodBodies,
       DISABLED_AnOutOfBlockMethodsCallReachesTheUnitsFunction) {
  Run(kUnitClassCalls);
  const std::vector<vpiHandle> kCalls =
      CallsIn(MethodOf(UnitScope(), "C", "d"));
  ASSERT_EQ(kCalls.size(), 1U);
  ASSERT_NE(Declared(UnitScope(), "f"), nullptr);
  EXPECT_EQ(Reached(vpiFunction, kCalls[0]), Declared(UnitScope(), "f"));
}

TEST_F(CallsInMethodBodies,
       DISABLED_ANameTheUnitAndTheClassDeclareIsTheClasss) {
  Run(kUnitClassCalls);
  const std::vector<vpiHandle> kCalls =
      CallsIn(MethodOf(UnitScope(), "C", "e"));
  ASSERT_EQ(kCalls.size(), 1U);
  vpiHandle g = MethodOf(UnitScope(), "C", "g");
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(Reached(vpiFunction, kCalls[0]), VpiObjectOf(g));
}

constexpr const char* kSiblingCalls =
    "module top;\n"
    "  class C; int r;\n"
    "    task t; endtask\n"
    "    function int g(); return 1; endfunction\n"
    "    task m; begin t(); r = g(); end endtask\n"
    "  endclass\n"
    "endmodule\n";

TEST_F(CallsInMethodBodies, DISABLED_AnUnprefixedSiblingCallIsAMethodCall) {
  Run(kSiblingCalls);
  EXPECT_EQ(KindsIn(MethodOf(By("top"), "C", "m")),
            (std::vector<int>{vpiMethodTaskCall, vpiMethodFuncCall}));
}

TEST_F(CallsInMethodBodies, DISABLED_AnUnprefixedSiblingCallReachesTheSibling) {
  Run(kSiblingCalls);
  const std::vector<vpiHandle> kCalls = CallsIn(MethodOf(By("top"), "C", "m"));
  ASSERT_EQ(kCalls.size(), 2U);
  vpiHandle t = MethodOf(By("top"), "C", "t");
  vpiHandle g = MethodOf(By("top"), "C", "g");
  ASSERT_NE(t, nullptr);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(Reached(vpiTask, kCalls[0]), VpiObjectOf(t));
  EXPECT_EQ(Reached(vpiFunction, kCalls[1]), VpiObjectOf(g));
}

TEST_F(CallsInMethodBodies, AnUnprefixedSiblingCallInTheDefnHasNoPrefix) {
  Run(kSiblingCalls);
  const std::vector<vpiHandle> kCalls = CallsIn(MethodOf(By("top"), "C", "m"));
  ASSERT_EQ(kCalls.size(), 2U);
  EXPECT_EQ(vpi_handle(vpiPrefix, kCalls[0]), nullptr);
  EXPECT_EQ(vpi_handle(vpiPrefix, kCalls[1]), nullptr);
}

class BuiltInMethodCalls : public CallsInMethodBodies {};

TEST_F(BuiltInMethodCalls, ABuiltInMethodTaskCallReachesNoTask) {
  Run("module top; semaphore s = new(1); mailbox m = new; int x;\n"
      "  process p;\n"
      "  task w; begin\n"
      "    s.get(1); m.put(1); m.get(x); m.peek(x); p.await();\n"
      "  end endtask\n"
      "endmodule\n");
  const std::vector<vpiHandle> kCalls =
      CallsIn(Named(vpiTaskFunc, By("top"), "w"));
  ASSERT_EQ(kCalls.size(), 5U);
  for (vpiHandle call : kCalls) {
    EXPECT_EQ(vpi_get(vpiType, call), vpiMethodTaskCall);
    EXPECT_EQ(vpi_handle(vpiTask, call), nullptr);
  }
}

TEST_F(BuiltInMethodCalls, ABuiltInMethodFuncCallReadsAsItsResult) {
  Run("module top; int q[$] = '{1, 2, 3}; string s = \"abcd\";\n"
      "  int r1, r2;\n"
      "  initial begin : b r1 = q.size(); r2 = s.len(); end\n"
      "endmodule\n");
  const std::vector<vpiHandle> kStmts = ObjectsOf(vpiStmt, By("top.b"));
  ASSERT_EQ(kStmts.size(), 2U);
  vpiHandle size = vpi_handle(vpiRhs, kStmts[0]);
  vpiHandle len = vpi_handle(vpiRhs, kStmts[1]);
  ASSERT_EQ(vpi_get(vpiType, size), vpiMethodFuncCall);
  ASSERT_EQ(vpi_get(vpiType, len), vpiMethodFuncCall);
  EXPECT_EQ(IntegerOf(size), 3);
  EXPECT_EQ(IntegerOf(len), 4);
}

TEST_F(BuiltInMethodCalls, AnOrderingMethodWithAWithClauseReachesNoWith) {
  Run("module top; int q[$] = '{3, 1, 2};\n"
      "  initial begin : b q.sort with (item); q.rsort with (item); end\n"
      "endmodule\n");
  const std::vector<vpiHandle> kStmts = ObjectsOf(vpiStmt, By("top.b"));
  ASSERT_EQ(kStmts.size(), 2U);
  for (vpiHandle call : kStmts) {
    EXPECT_EQ(vpi_get(vpiType, call), vpiMethodFuncCall);
    EXPECT_EQ(vpi_handle(vpiWith, call), nullptr);
  }
}

std::vector<vpiHandle> g_passed;

PLI_INT32 PassedCalltf(PLI_BYTE8*) {
  g_passed = {};
  vpiHandle call = vpi_handle(vpiSysTfCall, nullptr);
  vpiHandle args = call == nullptr ? nullptr : vpi_iterate(vpiArgument, call);
  for (vpiHandle arg = args == nullptr ? nullptr : vpi_scan(args);
       arg != nullptr; arg = vpi_scan(args)) {
    g_passed.push_back(arg);
  }
  return 0;
}

class ArgumentsOfEveryKind : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    g_passed = {};
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText("$passed");
    data.calltf = &PassedCalltf;
    ASSERT_NE(vpi_register_systf(&data), nullptr);
  }

  static void ExpectPassed(int type, const char* name) {
    ASSERT_EQ(g_passed.size(), 1U) << name;
    EXPECT_EQ(vpi_get(vpiType, g_passed[0]), type) << name;
    ASSERT_NE(By(name), nullptr) << name;
    EXPECT_EQ(VpiObjectOf(g_passed[0]), VpiObjectOf(By(name))) << name;
  }
};

TEST_F(ArgumentsOfEveryKind, AnInterfaceInstanceArgumentIsTheInterface) {
  Run("interface ifc; endinterface\n"
      "module top; ifc i(); initial $passed(i); endmodule\n");
  ExpectPassed(vpiInterface, "top.i");
}

TEST_F(ArgumentsOfEveryKind,
       DISABLED_AnInterfacePortArgumentIsTheBoundInterface) {
  Run("interface ifc; endinterface\n"
      "module m(ifc p); initial $passed(p); endmodule\n"
      "module top; ifc i(); m u(i); endmodule\n");
  ExpectPassed(vpiInterface, "top.i");
}

TEST_F(ArgumentsOfEveryKind, DISABLED_APrimitiveArgumentIsThePrimitive) {
  Run("module top; wire a, b; and g(a, b, b); initial $passed(g);\n"
      "endmodule\n");
  ExpectPassed(vpiGate, "top.g");
}

TEST_F(ArgumentsOfEveryKind, ANamedEventArgumentIsTheEvent) {
  Run("module top; event e; initial $passed(e); endmodule\n");
  ExpectPassed(vpiNamedEvent, "top.e");
}

TEST_F(ArgumentsOfEveryKind, ANamedEventArrayArgumentIsTheArray) {
  Run("module top; event ea[2]; initial $passed(ea); endmodule\n");
  ExpectPassed(vpiNamedEventArray, "top.ea");
}

class CallsThroughInterfacePorts : public CallsInMethodBodies {
 protected:
  static VpiObject* ReachedFrom(const char* block, int type, int relation) {
    const std::vector<vpiHandle> kStmts = ObjectsOf(vpiStmt, By(block));
    for (vpiHandle stmt : kStmts) {
      const bool kAssigned = vpi_get(vpiType, stmt) == vpiAssignment;
      vpiHandle call = kAssigned ? vpi_handle(vpiRhs, stmt) : stmt;
      if (vpi_get(vpiType, call) == type) return Reached(relation, call);
    }
    return nullptr;
  }
};

constexpr const char* kPortCalls =
    "interface ifc;\n"
    "  function int f(); return 7; endfunction\n"
    "  task t; endtask\n"
    "  modport mp(import f, import t);\n"
    "endinterface\n"
    "module m(ifc p); int x;\n"
    "  initial begin : b x = p.f(); p.t(); end\n"
    "endmodule\n"
    "module mm(ifc.mp p); int x;\n"
    "  initial begin : b x = p.f(); p.t(); end\n"
    "endmodule\n"
    "module top; ifc i1(), i2(); m u1(i1), u2(i2); mm w(i2); endmodule\n";

TEST_F(CallsThroughInterfacePorts,
       DISABLED_AFunctionCallReachesTheBoundFunction) {
  Run(kPortCalls);
  ASSERT_NE(Declared(By("top.i1"), "f"), nullptr);
  EXPECT_EQ(ReachedFrom("top.u1.b", vpiFuncCall, vpiFunction),
            Declared(By("top.i1"), "f"));
}

TEST_F(CallsThroughInterfacePorts, DISABLED_ATaskEnableReachesTheBoundTask) {
  Run(kPortCalls);
  ASSERT_NE(Declared(By("top.i1"), "t"), nullptr);
  EXPECT_EQ(ReachedFrom("top.u1.b", vpiTaskCall, vpiTask),
            Declared(By("top.i1"), "t"));
}

TEST_F(CallsThroughInterfacePorts,
       DISABLED_AModportPortsCallsReachTheBoundSubroutines) {
  Run(kPortCalls);
  ASSERT_NE(Declared(By("top.i2"), "f"), nullptr);
  ASSERT_NE(Declared(By("top.i2"), "t"), nullptr);
  EXPECT_EQ(ReachedFrom("top.w.b", vpiFuncCall, vpiFunction),
            Declared(By("top.i2"), "f"));
  EXPECT_EQ(ReachedFrom("top.w.b", vpiTaskCall, vpiTask),
            Declared(By("top.i2"), "t"));
}

TEST_F(CallsThroughInterfacePorts,
       DISABLED_EachInstancesCallReachesItsOwnBinding) {
  Run(kPortCalls);
  ASSERT_NE(Declared(By("top.i2"), "f"), nullptr);
  EXPECT_EQ(ReachedFrom("top.u2.b", vpiFuncCall, vpiFunction),
            Declared(By("top.i2"), "f"));
  EXPECT_NE(ReachedFrom("top.u2.b", vpiFuncCall, vpiFunction),
            Declared(By("top.i1"), "f"));
}

}  // namespace
}  // namespace delta
