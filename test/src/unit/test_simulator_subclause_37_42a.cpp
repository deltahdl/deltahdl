#include <gtest/gtest.h>

#include <algorithm>
#include <cstddef>
#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class TaskFuncCall : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

TEST_F(TaskFuncCall, CallKindsAreClassified) {
  EXPECT_TRUE(VpiIsTfCallType(vpiTaskCall));
  EXPECT_TRUE(VpiIsTfCallType(vpiFuncCall));
  EXPECT_TRUE(VpiIsTfCallType(vpiMethodFuncCall));
  EXPECT_TRUE(VpiIsTfCallType(vpiMethodTaskCall));
  EXPECT_TRUE(VpiIsTfCallType(vpiSysFuncCall));
  EXPECT_TRUE(VpiIsTfCallType(vpiSysTaskCall));
  EXPECT_FALSE(VpiIsTfCallType(vpiModule));
  EXPECT_FALSE(VpiIsTfCallType(vpiOperation));

  EXPECT_TRUE(VpiIsMethodCallType(vpiMethodFuncCall));
  EXPECT_TRUE(VpiIsMethodCallType(vpiMethodTaskCall));
  EXPECT_FALSE(VpiIsMethodCallType(vpiFuncCall));
  EXPECT_FALSE(VpiIsMethodCallType(vpiSysFuncCall));
}

TEST_F(TaskFuncCall, MethodPrefixReachesAppliedObject) {
  VpiObject packet;
  packet.type = vpiRefObj;

  VpiObject send;
  send.type = vpiMethodFuncCall;
  send.tf_prefix = &packet;

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiPrefix, VpiHandleOf(&send))), &packet);

  VpiObject func;
  func.type = vpiFuncCall;
  func.tf_prefix = &packet;
  EXPECT_EQ(vpi_handle(vpiPrefix, VpiHandleOf(&func)), nullptr);
}

TEST_F(TaskFuncCall, WithRelationAvailableOnlyForWithMethods) {
  VpiObject with_expr;
  with_expr.type = vpiOperation;

  VpiObject randomize;
  randomize.type = vpiMethodFuncCall;
  randomize.tf_with = &with_expr;
  randomize.tf_with_method = true;
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiWith, VpiHandleOf(&randomize))),
            &with_expr);

  VpiObject ordinary;
  ordinary.type = vpiMethodFuncCall;
  ordinary.tf_with = &with_expr;
  ordinary.tf_with_method = false;
  EXPECT_EQ(vpi_handle(vpiWith, VpiHandleOf(&ordinary)), nullptr);
}

TEST_F(TaskFuncCall, WithRelationReachesConstraintClause) {
  VpiObject with_constraint;
  with_constraint.type = vpiConstraint;

  VpiObject randomize;
  randomize.type = vpiMethodFuncCall;
  randomize.tf_with = &with_constraint;
  randomize.tf_with_method = true;
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiWith, VpiHandleOf(&randomize))),
            &with_constraint);
}

TEST_F(TaskFuncCall, InvokingSystemTfCallReachedWithNullRef) {
  VpiObject call;
  call.type = vpiSysTaskCall;
  ctx_.SetCurrentSystfCall(&call);

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiSysTfCall, nullptr)), &call);

  ctx_.SetCurrentSystfCall(nullptr);
  EXPECT_EQ(vpi_handle(vpiSysTfCall, nullptr), nullptr);
}

TEST_F(TaskFuncCall, UserSystfsRetrievedByIteration) {
  s_vpi_systf_data task = {};
  task.type = vpiSysTask;
  task.tfname = VpiText("$as_task");
  vpiHandle task_h = vpi_register_systf(&task);
  ASSERT_NE(task_h, nullptr);

  s_vpi_systf_data func = {};
  func.type = vpiSysFunc;
  func.sysfunctype = vpiIntFunc;
  func.tfname = VpiText("$as_func");
  vpiHandle func_h = vpi_register_systf(&func);
  ASSERT_NE(func_h, nullptr);
  vpiHandle it = vpi_iterate(vpiUserSystf, nullptr);
  ASSERT_NE(it, nullptr);
  int count = 0;
  bool saw_task = false;
  bool saw_func = false;
  while (vpiHandle h = vpi_scan(it)) {
    ++count;
    if (h == task_h) saw_task = true;
    if (h == func_h) saw_func = true;
  }
  EXPECT_EQ(count, 2);
  EXPECT_TRUE(saw_task);
  EXPECT_TRUE(saw_func);
}

TEST_F(TaskFuncCall, UserSystfIterationIsNullWhenNoneRegistered) {
  EXPECT_EQ(vpi_iterate(vpiUserSystf, nullptr), nullptr);
}

TEST_F(TaskFuncCall, EmptyAndNullArgumentsHaveDistinctRepresentations) {
  VpiObject empty;
  VpiMakeEmptyArgument(&empty);
  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(&empty)), vpiOperation);
  EXPECT_EQ(vpi_get(vpiOpType, VpiHandleOf(&empty)), vpiNullOp);

  VpiObject null_arg;
  VpiMakeNullArgument(&null_arg);
  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(&null_arg)), vpiConstant);
  EXPECT_EQ(vpi_get(vpiConstType, VpiHandleOf(&null_arg)), vpiNullConst);

  EXPECT_TRUE(VpiIsTfCallArgumentType(vpiOperation));
  EXPECT_TRUE(VpiIsTfCallArgumentType(vpiInterface));
  EXPECT_TRUE(VpiIsTfCallArgumentType(vpiModule));
  EXPECT_TRUE(VpiIsTfCallArgumentType(vpiNamedBegin));
  EXPECT_TRUE(VpiIsTfCallArgumentType(vpiGate));
  EXPECT_TRUE(VpiIsTfCallArgumentType(vpiNamedEvent));
  EXPECT_TRUE(VpiIsTfCallArgumentType(vpiNamedEventArray));
  EXPECT_FALSE(VpiIsTfCallArgumentType(vpiIf));
  EXPECT_FALSE(VpiIsTfCallArgumentType(vpiScope));
}

TEST_F(TaskFuncCall, ProtectedCallStillIteratesArguments) {
  VpiObject arg0;
  arg0.type = vpiOperation;
  VpiObject arg1;
  arg1.type = vpiNamedEvent;
  VpiObject not_arg;
  not_arg.type = vpiTypespec;
  VpiObject child;
  child.type = vpiConstant;

  VpiObject call;
  call.type = vpiSysTaskCall;
  call.is_protected = true;
  call.arguments = {&arg0, &not_arg, &arg1};
  call.children = {&child};

  vpiHandle it = vpi_iterate(vpiArgument, VpiHandleOf(&call));
  ASSERT_NE(it, nullptr);
  int count = 0;
  bool saw_arg0 = false;
  bool saw_arg1 = false;
  while (vpiHandle h = vpi_scan(it)) {
    ++count;
    if (VpiObjectOf(h) == &arg0) saw_arg0 = true;
    if (VpiObjectOf(h) == &arg1) saw_arg1 = true;
  }
  EXPECT_EQ(count, 2);
  EXPECT_TRUE(saw_arg0);
  EXPECT_TRUE(saw_arg1);

  EXPECT_EQ(vpi_iterate(vpiTypespec, VpiHandleOf(&call)), nullptr);
}

TEST_F(TaskFuncCall, BuiltinMethodHasNoFunctionOrTask) {
  VpiObject builtin_fn;
  builtin_fn.type = vpiMethodFuncCall;
  builtin_fn.builtin_method = true;
  VpiObject fn_obj;
  fn_obj.type = vpiFunction;
  builtin_fn.children = {&fn_obj};
  EXPECT_EQ(vpi_handle(vpiFunction, VpiHandleOf(&builtin_fn)), nullptr);

  VpiObject user_fn;
  user_fn.type = vpiMethodFuncCall;
  user_fn.builtin_method = false;
  VpiObject user_fn_obj;
  user_fn_obj.type = vpiFunction;
  user_fn.tf_decl = &user_fn_obj;
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiFunction, VpiHandleOf(&user_fn))),
            &user_fn_obj);

  VpiObject builtin_task;
  builtin_task.type = vpiMethodTaskCall;
  builtin_task.builtin_method = true;
  VpiObject task_obj;
  task_obj.type = vpiTask;
  builtin_task.children = {&task_obj};
  EXPECT_EQ(vpi_handle(vpiTask, VpiHandleOf(&builtin_task)), nullptr);
}

TEST_F(TaskFuncCall, FuncTypeReportedForFunctionCalls) {
  VpiObject func;
  func.type = vpiFuncCall;
  func.func_type = vpiIntFunc;
  EXPECT_EQ(vpi_get(vpiFuncType, VpiHandleOf(&func)), vpiIntFunc);

  VpiObject sys_func;
  sys_func.type = vpiSysFuncCall;
  sys_func.func_type = vpiRealFunc;
  EXPECT_EQ(vpi_get(vpiSysFuncType, VpiHandleOf(&sys_func)), vpiRealFunc);

  VpiObject untyped;
  untyped.type = vpiFuncCall;
  EXPECT_EQ(vpi_get(vpiFuncType, VpiHandleOf(&untyped)), 0);
}

TEST_F(TaskFuncCall, UserDefnReportedForCalls) {
  VpiObject user_sys;
  user_sys.type = vpiSysTaskCall;
  user_sys.user_defined = true;
  EXPECT_EQ(vpi_get(vpiUserDefn, VpiHandleOf(&user_sys)), 1);

  VpiObject builtin_sys;
  builtin_sys.type = vpiSysFuncCall;
  builtin_sys.user_defined = false;
  EXPECT_EQ(vpi_get(vpiUserDefn, VpiHandleOf(&builtin_sys)), 0);
}

TEST_F(TaskFuncCall, UserDefnReportedForMethodCalls) {
  VpiObject user_method;
  user_method.type = vpiMethodFuncCall;
  user_method.user_defined = true;
  EXPECT_EQ(vpi_get(vpiUserDefn, VpiHandleOf(&user_method)), 1);

  VpiObject builtin_method;
  builtin_method.type = vpiMethodTaskCall;
  builtin_method.user_defined = false;
  EXPECT_EQ(vpi_get(vpiUserDefn, VpiHandleOf(&builtin_method)), 0);
}

TEST_F(TaskFuncCall, DecompileReportedForSystemCalls) {
  VpiObject call;
  call.type = vpiSysTaskCall;
  call.decompile = "$strobe(a, b)";
  EXPECT_STREQ(vpi_get_str(vpiDecompile, VpiHandleOf(&call)), "$strobe(a, b)");

  VpiObject bare;
  bare.type = vpiSysFuncCall;
  EXPECT_EQ(vpi_get_str(vpiDecompile, VpiHandleOf(&bare)), nullptr);

  VpiObject method;
  method.type = vpiMethodTaskCall;
  method.decompile = "packet.send()";
  EXPECT_EQ(vpi_get_str(vpiDecompile, VpiHandleOf(&method)), nullptr);
}

class CallsOfARun : public VpiDesignRun {
 protected:
  static vpiHandle CallOnTheRight(const char* scope = "top") {
    vpiHandle it =
        vpi_iterate(vpiContAssign, vpi_handle_by_name(VpiText(scope), nullptr));
    if (it == nullptr) return nullptr;
    return vpi_handle(vpiRhs, vpi_scan(it));
  }
};

constexpr const char* kFunctionCall =
    "module top;\n"
    "  function automatic int f(int x); return x; endfunction\n"
    "  wire [31:0] a, y;\n"
    "  assign y = f(a);\n"
    "endmodule\n";

TEST_F(CallsOfARun, AFunctionCallIsAFuncCallObject) {
  Run(kFunctionCall);
  EXPECT_EQ(vpi_get(vpiType, CallOnTheRight()), vpiFuncCall);
}

TEST_F(CallsOfARun, AFunctionCallsArgumentIsTheNetPassed) {
  Run(kFunctionCall);
  EXPECT_EQ(NamesOf(vpiArgument, CallOnTheRight()),
            (std::vector<std::string>{"a"}));
}

TEST_F(CallsOfARun, ASystemFunctionCallIsASysFuncCallObject) {
  Run("module top; wire [7:0] a; wire [31:0] y; assign y = $countones(a); "
      "endmodule\n");
  EXPECT_EQ(vpi_get(vpiType, CallOnTheRight()), vpiSysFuncCall);
}

TEST_F(CallsOfARun, AFunctionCallReachesItsFunction) {
  Run(kFunctionCall);
  vpiHandle f = Named(vpiTaskFunc, By("top"), "f");
  ASSERT_NE(f, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiFunction, CallOnTheRight())),
            VpiObjectOf(f));
}

TEST_F(CallsOfARun, AGenerateBlockAssignmentReachesItsBlocksFunction) {
  Run("module top;\n"
      "  function int f(int x); return x; endfunction\n"
      "  if (1) begin : g\n"
      "    function int f(int x); return x + 1; endfunction\n"
      "    wire [31:0] w;\n"
      "    assign w = f(3);\n"
      "  end\n"
      "endmodule\n");
  vpiHandle f = Named(vpiTaskFunc, By("top.g"), "f");
  ASSERT_NE(f, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiFunction, CallOnTheRight("top.g"))),
            VpiObjectOf(f));
}

struct ProbeSighting {
  vpiHandle call;
  int user_defn;
  std::string decompile;
};
std::vector<ProbeSighting> g_probe_sightings;

PLI_INT32 ProbeCalltf(PLI_BYTE8*) {
  vpiHandle call = vpi_handle(vpiSysTfCall, nullptr);
  const char* decompile = vpi_get_str(vpiDecompile, call);
  g_probe_sightings.push_back({call, vpi_get(vpiUserDefn, call),
                               decompile != nullptr ? decompile : ""});
  return 0;
}

class CallStatementsOfARun : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    g_probe_sightings.clear();
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText("$probe");
    data.calltf = &ProbeCalltf;
    probe_ = vpi_register_systf(&data);
    ASSERT_NE(probe_, nullptr);
  }

  static vpiHandle BodyOf(const std::string& scope) {
    vpiHandle it = vpi_iterate(vpiProcess, By(scope));
    if (it == nullptr) return nullptr;
    return vpi_handle(vpiStmt, vpi_scan(it));
  }

  vpiHandle probe_ = nullptr;
};

TEST_F(CallStatementsOfARun, ASystemTaskCallIsAnObjectOfTheRun) {
  Run("module top; initial $display(\"hi\"); endmodule\n");
  vpiHandle call = BodyOf("top");
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(vpi_get(vpiType, call), vpiSysTaskCall);
  EXPECT_EQ(vpi_get_str(vpiName, call), nullptr);
  EXPECT_EQ(CalleeOf(call), "$display");
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiScope, call)), VpiObjectOf(By("top")));
  EXPECT_NE(vpi_handle(vpiProcess, call), nullptr);
}

TEST_F(CallStatementsOfARun, ATaskCallIsAnObjectOfTheRun) {
  Run("module top; task t; endtask initial t; endmodule\n");
  vpiHandle call = BodyOf("top");
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(vpi_get(vpiType, call), vpiTaskCall);
  EXPECT_EQ(vpi_get_str(vpiName, call), nullptr);
  EXPECT_EQ(CalleeOf(call), "t");
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiScope, call)), VpiObjectOf(By("top")));
}

TEST_F(CallStatementsOfARun, AFunctionCallStatementIsAFuncCall) {
  Run("module top; function void f(); endfunction initial f(); endmodule\n");
  vpiHandle call = BodyOf("top");
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(vpi_get(vpiType, call), vpiFuncCall);
  EXPECT_EQ(vpi_get_str(vpiName, call), nullptr);
  EXPECT_EQ(CalleeOf(call), "f");
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiScope, call)), VpiObjectOf(By("top")));
  EXPECT_NE(vpi_handle(vpiProcess, call), nullptr);
}

TEST_F(CallStatementsOfARun, ABuiltInSystemFunctionStatementIsASysFuncCall) {
  Run("module top; initial $random; endmodule\n");
  vpiHandle call = BodyOf("top");
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(vpi_get(vpiType, call), vpiSysFuncCall);
  EXPECT_EQ(vpi_get_str(vpiName, call), nullptr);
  EXPECT_EQ(CalleeOf(call), "$random");
  EXPECT_EQ(vpi_get(vpiUserDefn, call), 0);
  EXPECT_EQ(vpi_handle(vpiUserSystf, call), nullptr);
}

TEST_F(CallStatementsOfARun, AMethodFunctionCallStatementIsAMethodFuncCall) {
  Run("module top;\n"
      "  class C; function void go(); endfunction endclass\n"
      "  C obj = new;\n"
      "  initial obj.go();\n"
      "endmodule\n");
  vpiHandle call = BodyOf("top");
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(vpi_get(vpiType, call), vpiMethodFuncCall);
  EXPECT_EQ(vpi_get_str(vpiName, call), nullptr);
  EXPECT_EQ(CalleeOf(call), "go");
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiPrefix, call)), "obj");
  EXPECT_EQ(vpi_get(vpiUserDefn, call), 1);
}

constexpr const char* kMethodTaskCall =
    "module top;\n"
    "  class C; task run(); endtask endclass\n"
    "  C obj = new;\n"
    "  initial obj.run();\n"
    "endmodule\n";

TEST_F(CallStatementsOfARun, AMethodTaskCallIsAnObjectOfTheRun) {
  Run(kMethodTaskCall);
  vpiHandle call = BodyOf("top");
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(vpi_get(vpiType, call), vpiMethodTaskCall);
  EXPECT_EQ(vpi_get_str(vpiName, call), nullptr);
  EXPECT_EQ(CalleeOf(call), "run");
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiPrefix, call)), "obj");
  EXPECT_EQ(vpi_get(vpiUserDefn, call), 1);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiScope, call)), VpiObjectOf(By("top")));
}

TEST_F(CallStatementsOfARun, ACallStatementReachesItsDeclaration) {
  Run("module top; task t; endtask function void f(); endfunction\n"
      "  initial begin t; f(); end endmodule\n");
  vpiHandle task = CallOf(vpiTaskCall, BodyOf("top"), "t");
  vpiHandle func = CallOf(vpiFuncCall, BodyOf("top"), "f");
  ASSERT_NE(task, nullptr);
  ASSERT_NE(func, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiTask, task)),
            VpiObjectOf(Named(vpiTaskFunc, By("top"), "t")));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiFunction, func)),
            VpiObjectOf(Named(vpiTaskFunc, By("top"), "f")));
}

TEST_F(CallStatementsOfARun, APackageTaskCallReachesThePackageTask) {
  Run("package p; task t; endtask endpackage\n"
      "module top; initial p::t; endmodule\n");
  vpiHandle call = BodyOf("top");
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiTask, call)),
            VpiObjectOf(Named(vpiTaskFunc, By("p"), "t")));
}

TEST_F(CallStatementsOfARun, AMethodCallReachesItsMethod) {
  Run("module top;\n"
      "  class C; task run(); endtask function void go(); endfunction\n"
      "  endclass\n"
      "  C obj = new;\n"
      "  initial begin obj.run(); obj.go(); end\n"
      "endmodule\n");
  vpiHandle defn = Named(vpiClassDefn, By("top"), "C");
  vpiHandle run = CallOf(vpiMethodTaskCall, BodyOf("top"), "run");
  vpiHandle go = CallOf(vpiMethodFuncCall, BodyOf("top"), "go");
  ASSERT_NE(run, nullptr);
  ASSERT_NE(go, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiTask, run)),
            VpiObjectOf(Named(vpiMethods, defn, "run")));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiFunction, go)),
            VpiObjectOf(Named(vpiMethods, defn, "go")));
}

TEST_F(CallStatementsOfARun, AnInheritedMethodCallReachesTheBaseMethod) {
  Run("module top;\n"
      "  class B; task run(); endtask endclass\n"
      "  class D extends B; endclass\n"
      "  D obj = new;\n"
      "  initial obj.run();\n"
      "endmodule\n");
  vpiHandle base = Named(vpiClassDefn, By("top"), "B");
  vpiHandle call = BodyOf("top");
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiTask, call)),
            VpiObjectOf(Named(vpiMethods, base, "run")));
}

TEST_F(CallStatementsOfARun, AMethodTaskCallThroughAMemberChain) {
  Run("module top;\n"
      "  class B; task run(); endtask endclass\n"
      "  class H; B b = new; endclass\n"
      "  class A extends H; endclass\n"
      "  A a = new;\n"
      "  initial a.b.run();\n"
      "endmodule\n");
  vpiHandle call = BodyOf("top");
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(vpi_get(vpiType, call), vpiMethodTaskCall);
  EXPECT_EQ(vpi_get_str(vpiName, call), nullptr);
  EXPECT_EQ(CalleeOf(call), "run");
  EXPECT_EQ(vpi_get(vpiUserDefn, call), 1);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiTask, call)),
            VpiObjectOf(
                Named(vpiMethods, Named(vpiClassDefn, By("top"), "B"), "run")));
  vpiHandle prefix = vpi_handle(vpiPrefix, call);
  ASSERT_NE(prefix, nullptr);
  EXPECT_EQ(vpi_get(vpiType, prefix), vpiClassVar);
  EXPECT_EQ(VpiObjectOf(prefix),
            VpiObjectOf(Named(vpiVariables,
                              vpi_handle(vpiClassObj, By("top.a")), "b")));
}

TEST_F(CallStatementsOfARun, ABuiltInClassTaskCallIsNotUserDefined) {
  Run("module top; semaphore s = new(1); initial s.get(1); endmodule\n");
  vpiHandle call = BodyOf("top");
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(vpi_get(vpiType, call), vpiMethodTaskCall);
  EXPECT_EQ(vpi_get(vpiUserDefn, call), 0);
}

TEST_F(CallStatementsOfARun, ABuiltInClassFunctionCallIsAMethodFuncCall) {
  Run("module top; semaphore s = new(1); initial s.put(1); endmodule\n");
  vpiHandle call = BodyOf("top");
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(vpi_get(vpiType, call), vpiMethodFuncCall);
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiPrefix, call)), "s");
  EXPECT_EQ(vpi_get(vpiUserDefn, call), 0);
}

TEST_F(CallStatementsOfARun, ACallStatementReachesItsArguments) {
  Run("module top; int x; task t(input int a, input int b); endtask\n"
      "  initial begin $display(\"%d\", x); t(1, x); end endmodule\n");
  vpiHandle display = CallOf(vpiSysTaskCall, BodyOf("top"), "$display");
  vpiHandle task = CallOf(vpiTaskCall, BodyOf("top"), "t");
  ASSERT_NE(display, nullptr);
  ASSERT_NE(task, nullptr);
  vpiHandle it = vpi_iterate(vpiArgument, display);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(vpi_get(vpiType, vpi_scan(it)), vpiConstant);
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_scan(it)), "x");
  EXPECT_EQ(KindsOf(vpiArgument, task).size(), 2U);
}

TEST_F(CallStatementsOfARun, AnArgumentsFunctionCallReachesItsFunction) {
  Run("module top; int a; function int g(int x); return x; endfunction\n"
      "  task t(int v); endtask initial t(g(a)); endmodule\n");
  vpiHandle call = BodyOf("top");
  ASSERT_NE(call, nullptr);
  vpiHandle it = vpi_iterate(vpiArgument, call);
  ASSERT_NE(it, nullptr);
  vpiHandle arg = vpi_scan(it);
  EXPECT_EQ(vpi_get(vpiType, arg), vpiFuncCall);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiFunction, arg)),
            VpiObjectOf(Named(vpiTaskFunc, By("top"), "g")));
}

TEST_F(CallStatementsOfARun, AGenerateBlockCallReachesItsBlocksTask) {
  Run("module top; for (genvar i = 0; i < 2; i++) begin : g\n"
      "  task t(); endtask initial t; end endmodule\n");
  vpiHandle call = BodyOf("top.g[1]");
  ASSERT_NE(call, nullptr);
  vpiHandle task = Named(vpiTaskFunc, By("top.g[1]"), "t");
  ASSERT_NE(task, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiTask, call)), VpiObjectOf(task));
}

TEST_F(CallStatementsOfARun, TheInvokingCallIsTheModelsCallStatement) {
  Run("module m; initial $probe; endmodule\n"
      "module top; m u1(); m u2(); endmodule\n");
  std::vector<VpiObject*> seen;
  seen.reserve(g_probe_sightings.size());
  for (const ProbeSighting& sighting : g_probe_sightings) {
    seen.push_back(VpiObjectOf(sighting.call));
  }
  std::vector<VpiObject*> want{VpiObjectOf(BodyOf("top.u1")),
                               VpiObjectOf(BodyOf("top.u2"))};
  ASSERT_NE(want[0], nullptr);
  std::ranges::sort(seen);
  std::ranges::sort(want);
  EXPECT_EQ(seen, want);
}

TEST_F(CallStatementsOfARun, ARegisteredSystemTaskCallIsUserDefined) {
  Run("module top; initial begin $probe; $display(\"hi\"); end endmodule\n");
  ASSERT_EQ(g_probe_sightings.size(), 1U);
  EXPECT_EQ(g_probe_sightings[0].user_defn, 1);
  EXPECT_EQ(
      vpi_get(vpiUserDefn, CallOf(vpiSysTaskCall, BodyOf("top"), "$probe")), 1);
  EXPECT_EQ(
      vpi_get(vpiUserDefn, CallOf(vpiSysTaskCall, BodyOf("top"), "$display")),
      0);
}

TEST_F(CallStatementsOfARun, ASystemTaskCallReachesItsUserSystf) {
  Run("module top; initial begin $probe; $display(\"hi\"); end endmodule\n");
  ASSERT_EQ(g_probe_sightings.size(), 1U);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiUserSystf, g_probe_sightings[0].call)),
            VpiObjectOf(probe_));
  EXPECT_EQ(vpi_handle(vpiUserSystf,
                       CallOf(vpiSysTaskCall, BodyOf("top"), "$display")),
            nullptr);
}

vpiHandle g_peek_call = nullptr;

PLI_INT32 PeekCalltf(PLI_BYTE8*) {
  g_peek_call = vpi_handle(vpiSysTfCall, nullptr);
  return 0;
}

TEST_F(CallStatementsOfARun, ARegisteredSystemFunctionStatementIsASysFuncCall) {
  g_peek_call = nullptr;
  s_vpi_systf_data data = {};
  data.type = vpiSysFunc;
  data.sysfunctype = vpiIntFunc;
  data.tfname = VpiText("$peek");
  data.calltf = &PeekCalltf;
  vpiHandle peek = vpi_register_systf(&data);
  ASSERT_NE(peek, nullptr);
  Run("module top; initial $peek; endmodule\n");
  vpiHandle call = BodyOf("top");
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(vpi_get(vpiType, call), vpiSysFuncCall);
  EXPECT_EQ(vpi_get(vpiUserDefn, call), 1);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiUserSystf, call)), VpiObjectOf(peek));
  EXPECT_EQ(VpiObjectOf(g_peek_call), VpiObjectOf(call));
}

TEST_F(CallStatementsOfARun, ABuiltInSystemFunctionStatementIsNoSysTaskCall) {
  Run("module top; int a; real r = 2.0;\n"
      "  initial begin $random; $urandom; $cast(a, r); end endmodule\n");
  EXPECT_EQ(CallOf(vpiSysTaskCall, BodyOf("top"), "$random"), nullptr);
  EXPECT_EQ(CallOf(vpiSysTaskCall, BodyOf("top"), "$urandom"), nullptr);
  EXPECT_NE(CallOf(vpiSysTaskCall, BodyOf("top"), "$cast"), nullptr);
}

TEST_F(CallStatementsOfARun, AnArgumentNamingTheScopeAroundTheCallIsReached) {
  Run("module top; initial $printtimescale(top); endmodule\n");
  vpiHandle call = BodyOf("top");
  ASSERT_NE(call, nullptr);
  vpiHandle it = vpi_iterate(vpiArgument, call);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), VpiObjectOf(By("top")));
}

TEST_F(CallStatementsOfARun, AMethodTaskCallOnABlockVariableIsAnObject) {
  Run("module top;\n"
      "  class C; task run(); endtask endclass\n"
      "  int obj;\n"
      "  initial begin : b C obj; obj = new; obj.run(); end\n"
      "endmodule\n");
  vpiHandle call = CallOf(vpiMethodTaskCall, By("top.b"), "run");
  ASSERT_NE(call, nullptr);
  ASSERT_NE(By("top.b.obj"), nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiPrefix, call)),
            VpiObjectOf(By("top.b.obj")));
}

TEST_F(CallStatementsOfARun, ABuiltInMethodOfAModuleVariableIsAMethodFuncCall) {
  Run("module top; int q[$]; int aa[string]; string s = \"ab\";\n"
      "  typedef enum {A, B} e_t; e_t e;\n"
      "  initial begin q.push_back(1); aa.delete(); s.putc(0, \"c\");\n"
      "    e.next(); end\n"
      "endmodule\n");
  const std::vector<vpiHandle> kCalls =
      ObjectsOf(vpiMethodFuncCall, BodyOf("top"));
  const std::vector<std::string> kHolders{"q", "aa", "s", "e"};
  ASSERT_EQ(kCalls.size(), kHolders.size());
  for (std::size_t i = 0; i < kCalls.size(); ++i) {
    EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiPrefix, kCalls[i])),
                 kHolders[i].c_str());
    EXPECT_EQ(vpi_get(vpiUserDefn, kCalls[i]), 0) << i;
  }
}

TEST_F(CallStatementsOfARun, ABuiltInMethodOfABlockArrayIsAMethodFuncCall) {
  Run("module top; initial begin : b\n"
      "  int d[]; int f[2]; d.delete(); f.sort();\n"
      "end endmodule\n");
  const std::vector<vpiHandle> kCalls =
      ObjectsOf(vpiMethodFuncCall, By("top.b"));
  ASSERT_EQ(kCalls.size(), 2U);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiPrefix, kCalls[0])),
            VpiObjectOf(By("top.b.d")));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiPrefix, kCalls[1])),
            VpiObjectOf(By("top.b.f")));
}

TEST_F(CallStatementsOfARun, AnAssociativeArraysReductionIsAMethodFuncCall) {
  Run("module top; int aa[int]; initial aa.sum(); endmodule\n");
  vpiHandle call = BodyOf("top");
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(vpi_get(vpiType, call), vpiMethodFuncCall);
}

constexpr const char* kPackageTask = "package p; task t; endtask endpackage\n";

TEST_F(CallStatementsOfARun, ACallOfAnImportedPackageTaskIsATaskCall) {
  Run(std::string(kPackageTask) +
      "module top; import p::*; initial t; endmodule\n");
  vpiHandle call = BodyOf("top");
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(vpi_get(vpiType, call), vpiTaskCall);
  EXPECT_EQ(vpi_get_str(vpiName, call), nullptr);
  EXPECT_EQ(CalleeOf(call), "t");
}

TEST_F(CallStatementsOfARun, AScopedCallOfAPackageTaskIsATaskCall) {
  Run(std::string(kPackageTask) + "module top; initial p::t; endmodule\n");
  vpiHandle call = BodyOf("top");
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(vpi_get(vpiType, call), vpiTaskCall);
  EXPECT_EQ(vpi_get_str(vpiName, call), nullptr);
  EXPECT_EQ(CalleeOf(call), "t");
}

TEST_F(CallStatementsOfARun, ASystemTaskCallStatementDecompilesToItsCall) {
  Run("module top; int a; initial $display(\"a=%0d\",  a+1); endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, BodyOf("top")),
               "$display(\"a=%0d\", a + 1)");
}

TEST_F(CallStatementsOfARun, ASystemTaskCallWithNoArgumentsIsItsName) {
  Run("module top; initial $probe; endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, BodyOf("top")), "$probe");
}

TEST_F(CallStatementsOfARun, TheInvokingCallDecompilesToItsCall) {
  Run("module top; int a; task t; $probe(a*(a+1)); endtask\n"
      "  initial t; endmodule\n");
  ASSERT_EQ(g_probe_sightings.size(), 1U);
  EXPECT_EQ(g_probe_sightings[0].decompile, "$probe(a * (a + 1))");
}

TEST_F(CallStatementsOfARun, AnArgumentNamesTheBlocksDeclaration) {
  Run("module top; int x;\n"
      "  initial begin : b int x; $display(x); end\n"
      "endmodule\n");
  vpiHandle call = CallOf(vpiSysTaskCall, By("top.b"), "$display");
  ASSERT_NE(call, nullptr);
  vpiHandle it = vpi_iterate(vpiArgument, call);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), VpiObjectOf(By("top.b.x")));
}

TEST_F(TaskFuncCall, TheUserSystfIterationPassesOverOtherObjects) {
  ctx_.CreateModule("m", "m");
  s_vpi_systf_data task = {};
  task.type = vpiSysTask;
  task.tfname = VpiText("$only_task");
  vpiHandle task_h = vpi_register_systf(&task);
  vpiHandle it = vpi_iterate(vpiUserSystf, nullptr);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(vpi_scan(it), task_h);
  EXPECT_EQ(vpi_scan(it), nullptr);
}

}  // namespace
}  // namespace delta
