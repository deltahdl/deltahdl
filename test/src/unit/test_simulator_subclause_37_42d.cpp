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

// The call the calltf of the system function under test was last run with,
// which it reaches through vpiSysTfCall (§37.42 detail 3).
vpiHandle g_invoked_call = nullptr;

PLI_INT32 InvokedCallCalltf(PLI_BYTE8* /*user_data*/) {
  g_invoked_call = vpi_handle(vpiSysTfCall, nullptr);
  return 0;
}

// What the calltf of $args reached of its call's arguments, reading the value
// of each g_arg_reads times as it went; the call itself is g_invoked_call.
std::vector<vpiHandle> g_args_seen;
int g_arg_reads = 0;

PLI_INT32 ArgsCalltf(PLI_BYTE8* /*user_data*/) {
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

// §37.42: the calls a design's expressions make and the arguments a system
// task call is run with, read back from the model and from inside the calltf
// of a registration the case makes.
class CallsWithinADesign : public VpiDesignRun {
 protected:
  // Registers the system function `name`, returning a value of the kind
  // `func_type` names, whose calltf records the call it is run with.
  static vpiHandle RegisterFunction(const char* name, int func_type) {
    g_invoked_call = nullptr;
    s_vpi_systf_data data = {};
    data.type = vpiSysFunc;
    data.sysfunctype = func_type;
    data.tfname = VpiText(name);
    data.calltf = &InvokedCallCalltf;
    return vpi_register_systf(&data);
  }

  // Registers $args, whose calltf reads each argument `reads` times.
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

  // The right side of the one continuous assignment top holds.
  static vpiHandle AssignedRight() {
    const std::vector<vpiHandle> kAssigns = ObjectsOf(vpiContAssign, By("top"));
    return kAssigns.size() == 1 ? vpi_handle(vpiRhs, kAssigns[0]) : nullptr;
  }

  // The statement top's one procedure runs.
  static vpiHandle ProcedureStatement() {
    const std::vector<vpiHandle> kProcs = ObjectsOf(vpiProcess, By("top"));
    return kProcs.size() == 1 ? vpi_handle(vpiStmt, kProcs[0]) : nullptr;
  }

  // The value the variable `name` holds once the run is over.
  static int IntValueOf(const std::string& name) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(By(name), &value);
    return value.value.integer;
  }

  // The value top.i holds once `src` is run with $args reading its one
  // argument `reads` times; -1 where $args was not run with one argument.
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

// A call a continuous assignment makes is shaped as one a procedure makes:
// named after the function it calls, as a call within an expression is, and
// reaching the scope the assignment stands in (#7155)...
TEST_F(CallsWithinADesign, AContinuousAssignmentsCallIsNamedAndScoped) {
  Run(kAssignedCall);
  vpiHandle call = AssignedRight();
  ASSERT_NE(call, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, call), "f");
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiScope, call)), VpiObjectOf(By("top")));
}

// ...a built-in system function's call named after it and not user-defined...
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

// ...and a registered one's user-defined, reaching the systf its registration
// returned (detail 5).
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

// Detail 3: a registered system function written within a procedure's
// expression runs with the call the model holds for it, the right side of its
// assignment, which reaches the scope the assignment stands in (#7156).
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

// A func call reports through vpiFuncType the kind of value its function
// returns, the function's own (§37.41)...
TEST_F(CallsWithinADesign, AFunctionCallReportsItsFunctionsFuncType) {
  Run(kAssignedCall);
  vpiHandle f = Named(vpiTaskFunc, By("top"), "f");
  ASSERT_NE(f, nullptr);
  ASSERT_NE(vpi_get(vpiFuncType, f), 0);
  EXPECT_EQ(vpi_get(vpiFuncType, AssignedRight()), vpi_get(vpiFuncType, f));
}

// ...and a sys func call the kind its registration says the function returns,
// off the model and from inside its calltf alike (§38.37.1, #7154).
TEST_F(CallsWithinADesign, ASysFuncCallReportsItsRegistrationsFuncType) {
  ASSERT_NE(RegisterFunction("$peek", vpiSizedFunc), nullptr);
  Run("module top; int x; initial x = $peek(); endmodule\n");
  vpiHandle assign = ProcedureStatement();
  ASSERT_NE(assign, nullptr);
  EXPECT_EQ(vpi_get(vpiFuncType, vpi_handle(vpiRhs, assign)), vpiSizedFunc);
  ASSERT_NE(g_invoked_call, nullptr);
  EXPECT_EQ(vpi_get(vpiFuncType, g_invoked_call), vpiSizedFunc);
}

// Detail 8: a variable passed to a system task is reached as the variable
// itself, the object a walk of the design reaches, rather than a reference to
// it (#7157).
TEST_F(CallsWithinADesign, AVariableArgumentIsTheVariableItself) {
  ASSERT_NE(RegisterArgs(0), nullptr);
  Run("module top; logic [3:0] v; initial $args(v); endmodule\n");
  ASSERT_EQ(g_args_seen.size(), 1U);
  EXPECT_NE(vpi_get(vpiType, g_args_seen[0]), vpiRefObj);
  EXPECT_EQ(VpiObjectOf(g_args_seen[0]), VpiObjectOf(By("top.v")));
}

// Detail 8: the special value null passed to a system task is a constant of
// the null constant type, in its calltf and off the model alike (#7158).
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

// A design whose one system task call passes a call of a function bumping i,
// the argument's side effect (§37.3.5).
constexpr const char* kSteppingArgument =
    "module top; int i = 5;\n"
    "  function automatic int bump(); i = i + 1; return i; endfunction\n"
    "  initial $args(bump());\n"
    "endmodule\n";

// Detail 7: an argument is evaluated only when an application asks for its
// value, so $args(bump()) leaves i as it was where the calltf reads nothing...
TEST_F(CallsWithinADesign, AnArgumentNoApplicationReadsIsNeverEvaluated) {
  EXPECT_EQ(ValueAfterReads(kSteppingArgument, 0), 5);
}

// ...and is evaluated each time it is asked, its side effects with it, so two
// reads add two (§37.3.5, #6968).
TEST_F(CallsWithinADesign, AnArgumentIsEvaluatedEachTimeItIsRead) {
  EXPECT_EQ(ValueAfterReads(kSteppingArgument, 2), 7);
}

// A design whose one system task call steps i in its argument (§11.4.2).
constexpr const char* kIncrementArgument =
    "module top; int i = 5;\n"
    "  initial $args(i++);\n"
    "endmodule\n";

// An increment written as an argument is the model's operation, so it, too,
// steps i only when the calltf reads it, and each time it does (#7280).
TEST_F(CallsWithinADesign, AnIncrementNoApplicationReadsNeverSteps) {
  EXPECT_EQ(ValueAfterReads(kIncrementArgument, 0), 5);
}

TEST_F(CallsWithinADesign, AnIncrementStepsEachTimeItIsRead) {
  EXPECT_EQ(ValueAfterReads(kIncrementArgument, 2), 7);
}

// A call the body of a class's task writes is one the model holds no object
// for, so the call it runs with is one of its own. A system task's is
// unnamed all the same, being a statement (§37.60 detail 1), an argument it
// omits is a null operation and null passed to it is a null constant (detail
// 8)...
TEST_F(CallsWithinADesign, ATaskBodysSystemTaskCallIsUnnamed) {
  ASSERT_NE(RegisterArgs(0), nullptr);
  Run("module top; logic [3:0] v;\n"
      "  class C;\n"
      "    task t(input logic [3:0] w); $args(w, , null); endtask\n"
      "  endclass\n"
      "  C c;\n"
      "  initial begin c = new; c.t(v); end\n"
      "endmodule\n");
  ASSERT_NE(g_invoked_call, nullptr);
  EXPECT_EQ(vpi_get_str(vpiName, g_invoked_call), nullptr);
  ASSERT_EQ(g_args_seen.size(), 3U);
  EXPECT_EQ(vpi_get(vpiOpType, g_args_seen[1]), vpiNullOp);
  EXPECT_EQ(vpi_get(vpiType, g_args_seen[2]), vpiConstant);
  EXPECT_EQ(vpi_get(vpiConstType, g_args_seen[2]), vpiNullConst);
}

// ...while a system function's, which an expression may call, is named after
// the function (§37.42).
TEST_F(CallsWithinADesign, ATaskBodysSystemFunctionCallIsNamed) {
  ASSERT_NE(RegisterFunction("$peek", vpiIntFunc), nullptr);
  Run("module top;\n"
      "  class C; task t; int x; x = $peek(); endtask endclass\n"
      "  C c;\n"
      "  initial begin c = new; c.t(); end\n"
      "endmodule\n");
  ASSERT_NE(g_invoked_call, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, g_invoked_call), "$peek");
}

// A call the body of a class's function writes, which the model holds no
// object for either, builds each argument as the kind of expression its
// actual is (§37.58, §37.59), both when its compiletf runs, which reads no
// value (§36.8.2), and when its calltf does (§36.8.3).
TEST_F(CallsWithinADesign, AFunctionBodysCallBuildsEachArgumentKind) {
  g_args_seen.clear();
  g_arg_reads = 0;
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$kinds");
  data.compiletf = &ArgsCalltf;
  data.calltf = &ArgsCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
  Run("module top; int a, r;\n"
      "  function int f(int x); return x; endfunction\n"
      "  class K;\n"
      "    function int g();\n"
      "      $kinds(f(1), $clog2(4), 1, '1, 1.5, \"s\", a + 1);\n"
      "      return 0;\n"
      "    endfunction\n"
      "  endclass\n"
      "  K k;\n"
      "  initial begin k = new; r = k.g(); end\n"
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

// §36.8.2: the compiletf of a call a child instance's function writes runs
// before any instance is active, so the call it is given is one of its own,
// whose arguments are built as the kind of expression each actual is but hold
// no value, there being none to read yet.
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
