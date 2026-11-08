#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

vpiHandle g_invoked_call = nullptr;

PLI_INT32 InvokedCallCalltf(PLI_BYTE8*) {
  g_invoked_call = vpi_handle(vpiSysTfCall, nullptr);
  return 0;
}

std::vector<vpiHandle> g_args_seen;
int g_arg_reads = 0;

PLI_INT32 ArgsCalltf(PLI_BYTE8*) {
  g_args_seen.clear();
  g_invoked_call = vpi_handle(vpiSysTfCall, nullptr);
  vpiHandle it = vpi_iterate(vpiArgument, g_invoked_call);
  if (it == nullptr) return 0;
  while (vpiHandle arg = vpi_scan(it)) {
    g_args_seen.push_back(arg);
    for (int read = 0; read < g_arg_reads; ++read) {
      s_vpi_value value = {};
      value.format = vpiIntVal;
      vpi_get_value(arg, &value);
    }
  }
  return 0;
}

class CallsWithinADesign : public VpiDesignRun {
 protected:
  static vpiHandle RegisterFunction(const char* name, int func_type) {
    g_invoked_call = nullptr;
    s_vpi_systf_data data = {};
    data.type = vpiSysFunc;
    data.sysfunctype = func_type;
    data.tfname = VpiText(name);
    data.calltf = &InvokedCallCalltf;
    return vpi_register_systf(&data);
  }

  static vpiHandle RegisterArgs(int reads) {
    g_invoked_call = nullptr;
    g_args_seen.clear();
    g_arg_reads = reads;
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText("$args");
    data.calltf = &ArgsCalltf;
    return vpi_register_systf(&data);
  }

  static vpiHandle AssignedRight() {
    const std::vector<vpiHandle> kAssigns = ObjectsOf(vpiContAssign, By("top"));
    return kAssigns.size() == 1 ? vpi_handle(vpiRhs, kAssigns[0]) : nullptr;
  }

  static vpiHandle ProcedureStatement() {
    const std::vector<vpiHandle> kProcs = ObjectsOf(vpiProcess, By("top"));
    return kProcs.size() == 1 ? vpi_handle(vpiStmt, kProcs[0]) : nullptr;
  }

  static int IntValueOf(const std::string& name) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(By(name), &value);
    return value.value.integer;
  }

  int ValueAfterReads(const char* src, int reads) {
    if (RegisterArgs(reads) == nullptr) return -1;
    Run(src);
    return g_args_seen.size() == 1 ? IntValueOf("top.i") : -1;
  }
};

constexpr const char* kAssignedCall =
    "module top;\n"
    "  function automatic int f(int x); return x; endfunction\n"
    "  wire [31:0] a, y;\n"
    "  assign y = f(a);\n"
    "endmodule\n";

TEST_F(CallsWithinADesign, AContinuousAssignmentsCallIsNamedAndScoped) {
  Run(kAssignedCall);
  vpiHandle call = AssignedRight();
  ASSERT_NE(call, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, call), "f");
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiScope, call)), VpiObjectOf(By("top")));
}

TEST_F(CallsWithinADesign, AContinuousAssignmentsSystemCallIsNamed) {
  Run("module top; wire [7:0] a; wire [31:0] y; assign y = $countones(a);\n"
      "endmodule\n");
  vpiHandle call = AssignedRight();
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(vpi_get(vpiType, call), vpiSysFuncCall);
  EXPECT_STREQ(vpi_get_str(vpiName, call), "$countones");
  EXPECT_EQ(vpi_get(vpiUserDefn, call), 0);
  EXPECT_EQ(vpi_handle(vpiUserSystf, call), nullptr);
}

TEST_F(CallsWithinADesign, AContinuousAssignmentsRegisteredCallReachesSystf) {
  vpiHandle tally = RegisterFunction("$tally", vpiIntFunc);
  ASSERT_NE(tally, nullptr);
  Run("module top; wire [31:0] a, y; assign y = $tally(a); endmodule\n");
  vpiHandle call = AssignedRight();
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(vpi_get(vpiType, call), vpiSysFuncCall);
  EXPECT_STREQ(vpi_get_str(vpiName, call), "$tally");
  EXPECT_EQ(vpi_get(vpiUserDefn, call), 1);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiUserSystf, call)), VpiObjectOf(tally));
}

TEST_F(CallsWithinADesign, AnExpressionsSystemCallRunsAsTheModelsCall) {
  ASSERT_NE(RegisterFunction("$peek", vpiIntFunc), nullptr);
  Run("module top; int x, a; initial x = $peek(a); endmodule\n");
  vpiHandle assign = ProcedureStatement();
  ASSERT_NE(assign, nullptr);
  vpiHandle call = vpi_handle(vpiRhs, assign);
  ASSERT_NE(call, nullptr);
  ASSERT_NE(g_invoked_call, nullptr);
  EXPECT_EQ(VpiObjectOf(g_invoked_call), VpiObjectOf(call));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiScope, g_invoked_call)),
            VpiObjectOf(By("top")));
}

TEST_F(CallsWithinADesign, AFunctionCallReportsItsFunctionsFuncType) {
  Run(kAssignedCall);
  vpiHandle f = Named(vpiTaskFunc, By("top"), "f");
  ASSERT_NE(f, nullptr);
  ASSERT_NE(vpi_get(vpiFuncType, f), 0);
  EXPECT_EQ(vpi_get(vpiFuncType, AssignedRight()), vpi_get(vpiFuncType, f));
}

TEST_F(CallsWithinADesign, ASysFuncCallReportsItsRegistrationsFuncType) {
  ASSERT_NE(RegisterFunction("$peek", vpiSizedFunc), nullptr);
  Run("module top; int x; initial x = $peek(); endmodule\n");
  vpiHandle assign = ProcedureStatement();
  ASSERT_NE(assign, nullptr);
  EXPECT_EQ(vpi_get(vpiFuncType, vpi_handle(vpiRhs, assign)), vpiSizedFunc);
  ASSERT_NE(g_invoked_call, nullptr);
  EXPECT_EQ(vpi_get(vpiFuncType, g_invoked_call), vpiSizedFunc);
}

TEST_F(CallsWithinADesign, AVariableArgumentIsTheVariableItself) {
  ASSERT_NE(RegisterArgs(0), nullptr);
  Run("module top; logic [3:0] v; initial $args(v); endmodule\n");
  ASSERT_EQ(g_args_seen.size(), 1U);
  EXPECT_NE(vpi_get(vpiType, g_args_seen[0]), vpiRefObj);
  EXPECT_EQ(VpiObjectOf(g_args_seen[0]), VpiObjectOf(By("top.v")));
}

TEST_F(CallsWithinADesign, ANullArgumentIsANullConstant) {
  ASSERT_NE(RegisterArgs(0), nullptr);
  Run("module top; initial $args(null); endmodule\n");
  ASSERT_EQ(g_args_seen.size(), 1U);
  EXPECT_EQ(vpi_get(vpiType, g_args_seen[0]), vpiConstant);
  EXPECT_EQ(vpi_get(vpiConstType, g_args_seen[0]), vpiNullConst);
  const std::vector<vpiHandle> kWritten =
      ObjectsOf(vpiArgument, ProcedureStatement());
  ASSERT_EQ(kWritten.size(), 1U);
  EXPECT_EQ(vpi_get(vpiConstType, kWritten[0]), vpiNullConst);
}

constexpr const char* kSteppingArgument =
    "module top; int i = 5;\n"
    "  function automatic int bump(); i = i + 1; return i; endfunction\n"
    "  initial $args(bump());\n"
    "endmodule\n";

TEST_F(CallsWithinADesign, AnArgumentNoApplicationReadsIsNeverEvaluated) {
  EXPECT_EQ(ValueAfterReads(kSteppingArgument, 0), 5);
}

TEST_F(CallsWithinADesign, AnArgumentIsEvaluatedEachTimeItIsRead) {
  EXPECT_EQ(ValueAfterReads(kSteppingArgument, 2), 7);
}

constexpr const char* kIncrementArgument =
    "module top; int i = 5;\n"
    "  initial $args(i++);\n"
    "endmodule\n";

TEST_F(CallsWithinADesign, AnIncrementNoApplicationReadsNeverSteps) {
  EXPECT_EQ(ValueAfterReads(kIncrementArgument, 0), 5);
}

TEST_F(CallsWithinADesign, AnIncrementStepsEachTimeItIsRead) {
  EXPECT_EQ(ValueAfterReads(kIncrementArgument, 2), 7);
}

TEST_F(CallsWithinADesign, APackageTaskBodysCallIsThePackagesStatement) {
  ASSERT_NE(RegisterArgs(0), nullptr);
  Run("package pk; task t; $args(); endtask endpackage\n"
      "module top; initial pk::t(); endmodule\n");
  ASSERT_NE(g_invoked_call, nullptr);
  vpiHandle task = Named(vpiTaskFunc, By("pk"), "t");
  ASSERT_NE(task, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, task)),
            VpiObjectOf(g_invoked_call));
}

TEST_F(CallsWithinADesign, ATaskBodysSystemTaskCallIsUnnamed) {
  ASSERT_NE(RegisterArgs(0), nullptr);
  Run("package pk;\n"
      "  task t(input logic [3:0] w); $args(w, , null); endtask\n"
      "endpackage\n"
      "module top; logic [3:0] v;\n"
      "  initial pk::t(v);\n"
      "endmodule\n");
  ASSERT_NE(g_invoked_call, nullptr);
  EXPECT_EQ(vpi_get_str(vpiName, g_invoked_call), nullptr);
  ASSERT_EQ(g_args_seen.size(), 3U);
  EXPECT_EQ(vpi_get(vpiOpType, g_args_seen[1]), vpiNullOp);
  EXPECT_EQ(vpi_get(vpiType, g_args_seen[2]), vpiConstant);
  EXPECT_EQ(vpi_get(vpiConstType, g_args_seen[2]), vpiNullConst);
}

TEST_F(CallsWithinADesign, ATaskBodysSystemFunctionCallIsNamed) {
  ASSERT_NE(RegisterFunction("$peek", vpiIntFunc), nullptr);
  Run("package pk; task t; int x; x = $peek(); endtask endpackage\n"
      "module top;\n"
      "  initial pk::t();\n"
      "endmodule\n");
  ASSERT_NE(g_invoked_call, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, g_invoked_call), "$peek");
}

TEST_F(CallsWithinADesign, AFunctionBodysCallBuildsEachArgumentKind) {
  g_args_seen.clear();
  g_arg_reads = 0;
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$kinds");
  data.compiletf = &ArgsCalltf;
  data.calltf = &ArgsCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
  Run("package pk; int a;\n"
      "  function int f(int x); return x; endfunction\n"
      "  function int g();\n"
      "    $kinds(f(1), $clog2(4), 1, '1, 1.5, \"s\", a + 1);\n"
      "    return 0;\n"
      "  endfunction\n"
      "endpackage\n"
      "module top; int r;\n"
      "  initial r = pk::g();\n"
      "endmodule\n");
  std::vector<int> kinds;
  kinds.reserve(g_args_seen.size());
  for (vpiHandle arg : g_args_seen) kinds.push_back(vpi_get(vpiType, arg));
  EXPECT_EQ(kinds, (std::vector<int>{vpiFuncCall, vpiSysFuncCall, vpiConstant,
                                     vpiConstant, vpiConstant, vpiConstant,
                                     vpiOperation}));
  ASSERT_EQ(g_args_seen.size(), 7U);
  EXPECT_EQ(vpi_get(vpiConstType, g_args_seen[2]), vpiIntConst);
  EXPECT_EQ(vpi_get(vpiConstType, g_args_seen[4]), vpiRealConst);
  EXPECT_EQ(vpi_get(vpiConstType, g_args_seen[5]), vpiStringConst);
}

TEST_F(CallsWithinADesign, ATwoInstanceCallsCompiletfBuildsItsOwnArguments) {
  g_args_seen.clear();
  g_arg_reads = 0;
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$kinds");
  data.compiletf = &ArgsCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
  Run("int gv;\n"
      "module child; int a;\n"
      "  function int f(int x); return x; endfunction\n"
      "  function int g();\n"
      "    $kinds(gv, f(1), $clog2(4), 1, '1, 1.5, \"s\", a + 1, , null);\n"
      "    return 0;\n"
      "  endfunction\n"
      "endmodule\n"
      "module top; child u1 (), u2 (); endmodule\n");
  std::vector<int> kinds;
  kinds.reserve(g_args_seen.size());
  for (vpiHandle arg : g_args_seen) kinds.push_back(vpi_get(vpiType, arg));
  EXPECT_EQ(kinds, (std::vector<int>{vpiRefObj, vpiFuncCall, vpiSysFuncCall,
                                     vpiConstant, vpiConstant, vpiConstant,
                                     vpiConstant, vpiOperation, vpiOperation,
                                     vpiConstant}));
  ASSERT_EQ(g_args_seen.size(), 10U);
  EXPECT_STREQ(vpi_get_str(vpiName, g_args_seen[0]), "gv");
  EXPECT_EQ(vpi_get(vpiConstType, g_args_seen[3]), vpiIntConst);
  EXPECT_EQ(vpi_get(vpiConstType, g_args_seen[5]), vpiRealConst);
  EXPECT_EQ(vpi_get(vpiConstType, g_args_seen[6]), vpiStringConst);
  EXPECT_EQ(vpi_get(vpiOpType, g_args_seen[8]), vpiNullOp);
  EXPECT_EQ(vpi_get(vpiConstType, g_args_seen[9]), vpiNullConst);
}

TEST_F(CallsWithinADesign, AChildsCompiletfBuildsArgumentsOfItsOwn) {
  g_args_seen.clear();
  g_arg_reads = 0;
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$kids");
  data.compiletf = &ArgsCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
  Run("module child; int r;\n"
      "  function int g(); $kids(2); return 0; endfunction\n"
      "endmodule\n"
      "module top; child u (); endmodule\n");
  ASSERT_EQ(g_args_seen.size(), 1U);
  EXPECT_EQ(vpi_get(vpiType, g_args_seen[0]), vpiConstant);
}

}  // namespace
}  // namespace delta
