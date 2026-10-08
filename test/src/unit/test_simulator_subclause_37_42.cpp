#include <gtest/gtest.h>

#include <algorithm>
#include <string>
#include <utility>
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

// §37.42 Task and function call: the object model diagram for a tf call - the
// task call, function call, method task/func call, and system task/func call
// the diagram groups under "tf call". A call iterates its arguments
// (vpiArgument); a method call additionally reaches the object it is applied to
// (vpiPrefix) and a with clause (vpiWith) when the method accepts one. The
// diagram carries eleven numbered Details; these tests observe the production
// code that applies the ones this subclause owns: the vpiPrefix relation
// (detail 2), the vpiWith availability rule (detail 1), the invoking-systf
// handle (detail 3), the vpiUserSystf iteration (detail 6), the empty/null
// argument representations (detail 8), the vpiDecompile decompiled-call rule
// (detail 9), the protected-call argument-iteration carve-out (detail 10), and
// the built-in-method NULL rule for vpiFunction/vpiTask (detail 11). They also
// observe the tf-call scalar properties the diagram draws: the vpiFuncType
// "-> type" of a function call and the vpiUserDefn "-> user-defined" flag
// (detail 5).

// The fixture installs a context so the public vpi_get/vpi_iterate/vpi_handle
// entry points run their real dispatch over the test objects.
class TaskFuncCall : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// Diagram (tf call class members): the classifier recognizes the six call kinds
// the "tf call" class groups, and distinguishes the two method-call kinds that
// the vpiPrefix/vpiWith relations and the built-in-method rule are scoped to.
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
  EXPECT_FALSE(VpiIsMethodCallType(vpiFuncCall));  // a plain func call
  EXPECT_FALSE(VpiIsMethodCallType(vpiSysFuncCall));
}

// Detail 2: vpiPrefix of a method call reaches the object the method is applied
// to (the class var "packet" in "packet.send()"). A tf call that is not a
// method call carries no prefix, so vpiPrefix on it reports NULL.
TEST_F(TaskFuncCall, MethodPrefixReachesAppliedObject) {
  VpiObject packet;  // the class variable the method is applied to
  packet.type = vpiRefObj;

  VpiObject send;
  send.type = vpiMethodFuncCall;
  send.tf_prefix = &packet;

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiPrefix, VpiHandleOf(&send))), &packet);

  // A plain function call is not a method call: vpiPrefix does not apply, even
  // when a prefix object happens to be set, so the gating reports NULL.
  VpiObject func;
  func.type = vpiFuncCall;
  func.tf_prefix = &packet;
  EXPECT_EQ(vpi_handle(vpiPrefix, VpiHandleOf(&func)), nullptr);
}

// Detail 1: the vpiWith relation is available only for the methods that accept
// a with clause - the randomize methods and the array locator methods. A method
// call flagged as one of those reaches its with clause; any other method call
// reports NULL through vpiWith even when a with object is attached.
TEST_F(TaskFuncCall, WithRelationAvailableOnlyForWithMethods) {
  VpiObject with_expr;
  with_expr.type = vpiOperation;

  VpiObject randomize;
  randomize.type = vpiMethodFuncCall;
  randomize.tf_with = &with_expr;
  randomize.tf_with_method = true;  // a randomize/array-locator method
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiWith, VpiHandleOf(&randomize))),
            &with_expr);

  // An ordinary method call does not accept a with clause: the relation is
  // unavailable, so vpiWith reports NULL despite the attached object.
  VpiObject ordinary;
  ordinary.type = vpiMethodFuncCall;
  ordinary.tf_with = &with_expr;
  ordinary.tf_with_method = false;
  EXPECT_EQ(vpi_handle(vpiWith, VpiHandleOf(&ordinary)), nullptr);
}

// Detail 1 (figure, second target form): the vpiWith relation admits two kinds
// of with clause - a plain expression (the array locator "with (item)") and a
// constraint (the "randomize() with { ... }" block). The prior test covers the
// expression target; here the with clause is a constraint object, and vpiWith
// on the randomize method reaches it just the same.
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

// Detail 3: the system task or function that invoked the application is reached
// with vpi_handle(vpiSysTfCall, NULL).
TEST_F(TaskFuncCall, InvokingSystemTfCallReachedWithNullRef) {
  VpiObject call;
  call.type = vpiSysTaskCall;
  ctx_.SetCurrentSystfCall(&call);

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiSysTfCall, nullptr)), &call);

  // With no system tf call active the relation reports NULL.
  ctx_.SetCurrentSystfCall(nullptr);
  EXPECT_EQ(vpi_handle(vpiSysTfCall, nullptr), nullptr);
}

// Detail 6: every user-defined system task or function is retrieved with
// vpi_iterate(vpiUserSystf, NULL). The registered systf objects are collected
// regardless of their underlying object kind, and unrelated objects are not.
TEST_F(TaskFuncCall, UserSystfsRetrievedByIteration) {
  s_vpi_systf_data task = {};
  task.type = vpiSysTask;
  task.tfname = VpiText("$as_task");
  vpiHandle task_h = vpi_register_systf(&task);
  ASSERT_NE(task_h, nullptr);

  s_vpi_systf_data func = {};
  func.type = vpiSysFunc;
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

// Detail 6 (edge): when no user-defined system task or function has been
// registered, the vpiUserSystf iteration has nothing to walk, so vpi_iterate
// reports a null handle rather than an iterator that scans to nothing.
TEST_F(TaskFuncCall, UserSystfIterationIsNullWhenNoneRegistered) {
  EXPECT_EQ(vpi_iterate(vpiUserSystf, nullptr), nullptr);
}

// Detail 8: an omitted (empty) argument and a `null`-valued argument have
// distinct representations - an empty argument is a vpiOperation whose
// vpiOpType is vpiNullOp, while a null argument is a vpiConstant whose
// vpiConstType is vpiNullConst. The representations are observed through the
// public vpi_get dispatch. The argument-kind classifier additionally pins which
// object kinds the vpiArgument relation reaches.
TEST_F(TaskFuncCall, EmptyAndNullArgumentsHaveDistinctRepresentations) {
  VpiObject empty;
  VpiMakeEmptyArgument(&empty);
  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(&empty)), vpiOperation);
  EXPECT_EQ(vpi_get(vpiOpType, VpiHandleOf(&empty)), vpiNullOp);

  VpiObject null_arg;
  VpiMakeNullArgument(&null_arg);
  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(&null_arg)), vpiConstant);
  EXPECT_EQ(vpi_get(vpiConstType, VpiHandleOf(&null_arg)), vpiNullConst);

  // The vpiArgument relation reaches exprs, an interface expr, a scope, a
  // primitive, and named events; `scope` is a class whose kinds a module and a
  // named begin are (§37.4.1), and a statement is not an argument.
  EXPECT_TRUE(VpiIsTfCallArgumentType(vpiOperation));  // an expr kind
  EXPECT_TRUE(VpiIsTfCallArgumentType(vpiInterface));  // an interface expr kind
  EXPECT_TRUE(VpiIsTfCallArgumentType(vpiModule));     // a scope kind
  EXPECT_TRUE(VpiIsTfCallArgumentType(vpiNamedBegin));
  EXPECT_TRUE(VpiIsTfCallArgumentType(vpiGate));  // a primitive
  EXPECT_TRUE(VpiIsTfCallArgumentType(vpiNamedEvent));
  EXPECT_TRUE(VpiIsTfCallArgumentType(vpiNamedEventArray));
  EXPECT_FALSE(VpiIsTfCallArgumentType(vpiIf));     // a statement
  EXPECT_FALSE(VpiIsTfCallArgumentType(vpiScope));  // a class, not a kind
}

// Detail 10: iterating a protected object's relationships is normally an error,
// but a protected system task or function call still allows iteration over its
// vpiArgument relation. The argument iteration collects only the call's
// argument objects (excluding one of a kind no argument is, and the call's
// children), while any other relation on the same protected call is still
// refused.
TEST_F(TaskFuncCall, ProtectedCallStillIteratesArguments) {
  VpiObject arg0;
  arg0.type = vpiOperation;  // an argument expression
  VpiObject arg1;
  arg1.type = vpiNamedEvent;  // a named-event argument
  VpiObject not_arg;
  not_arg.type = vpiTypespec;  // a kind that is not a call argument
  VpiObject child;
  child.type = vpiConstant;  // a child, which is no argument

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
  EXPECT_EQ(count, 2);  // the non-argument child is excluded
  EXPECT_TRUE(saw_arg0);
  EXPECT_TRUE(saw_arg1);

  // Iterating any other relation of the protected call is still an error - no
  // iterator is produced.
  EXPECT_EQ(vpi_iterate(vpiTypespec, VpiHandleOf(&call)), nullptr);
}

// Detail 11: a built-in method func call has no user function object, so
// vpiFunction reports NULL; a built-in method task call likewise reports NULL
// for vpiTask. A user-defined (non-built-in) method call reaches its
// function/task.
TEST_F(TaskFuncCall, BuiltinMethodHasNoFunctionOrTask) {
  VpiObject builtin_fn;
  builtin_fn.type = vpiMethodFuncCall;
  builtin_fn.builtin_method = true;
  VpiObject fn_obj;  // would be the function were this user-defined
  fn_obj.type = vpiFunction;
  builtin_fn.children = {&fn_obj};
  EXPECT_EQ(vpi_handle(vpiFunction, VpiHandleOf(&builtin_fn)), nullptr);

  // A user-defined method func call reaches its function object.
  VpiObject user_fn;
  user_fn.type = vpiMethodFuncCall;
  user_fn.builtin_method = false;
  VpiObject user_fn_obj;
  user_fn_obj.type = vpiFunction;
  user_fn.tf_decl = &user_fn_obj;
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiFunction, VpiHandleOf(&user_fn))),
            &user_fn_obj);

  // The same rule governs a built-in method task call through vpiTask.
  VpiObject builtin_task;
  builtin_task.type = vpiMethodTaskCall;
  builtin_task.builtin_method = true;
  VpiObject task_obj;
  task_obj.type = vpiTask;
  builtin_task.children = {&task_obj};
  EXPECT_EQ(vpi_handle(vpiTask, VpiHandleOf(&builtin_task)), nullptr);
}

// Diagram property (-> type): a func call and a sys func call report their
// function return-type class through vpiFuncType (vpiSysFuncType is the same
// constant). The stored type code is handed straight back; a call that carries
// no type - and an object that is not a function call - reports zero.
TEST_F(TaskFuncCall, FuncTypeReportedForFunctionCalls) {
  VpiObject func;
  func.type = vpiFuncCall;
  func.func_type = vpiIntFunc;
  EXPECT_EQ(vpi_get(vpiFuncType, VpiHandleOf(&func)), vpiIntFunc);

  // A system function call reports through the same property (vpiSysFuncType is
  // #defined equal to vpiFuncType).
  VpiObject sys_func;
  sys_func.type = vpiSysFuncCall;
  sys_func.func_type = vpiRealFunc;
  EXPECT_EQ(vpi_get(vpiSysFuncType, VpiHandleOf(&sys_func)), vpiRealFunc);

  // A call that stored no function type reports zero.
  VpiObject untyped;
  untyped.type = vpiFuncCall;
  EXPECT_EQ(vpi_get(vpiFuncType, VpiHandleOf(&untyped)), 0);
}

// Detail 5 (property): a method call and a system task/function call report
// whether they are user-defined through the vpiUserDefn Boolean property; a
// call not so flagged reports false.
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

// Detail 5 / figure (method-call position): vpiUserDefn is drawn on the method
// calls as well as the system calls. A method func or task call reports its
// user-defined flag through the same property; the accepting and negative forms
// are both observed on a method call.
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

// Detail 9: a system task or function call reports, through the vpiDecompile
// string property, a functionally equivalent call to the source text. A call
// that carries no decompiled form, and an object that is not a system call,
// report null rather than an empty string.
TEST_F(TaskFuncCall, DecompileReportedForSystemCalls) {
  VpiObject call;
  call.type = vpiSysTaskCall;
  call.decompile = "$strobe(a, b)";
  EXPECT_STREQ(vpi_get_str(vpiDecompile, VpiHandleOf(&call)), "$strobe(a, b)");

  // A system call with no stored decompiled form reports null.
  VpiObject bare;
  bare.type = vpiSysFuncCall;
  EXPECT_EQ(vpi_get_str(vpiDecompile, VpiHandleOf(&bare)), nullptr);

  // The property is drawn only on system calls: an ordinary method call reports
  // null even when a decompiled string is attached.
  VpiObject method;
  method.type = vpiMethodTaskCall;
  method.decompile = "packet.send()";
  EXPECT_EQ(vpi_get_str(vpiDecompile, VpiHandleOf(&method)), nullptr);
}

// A design whose one continuous assignment's right side is a call, run with a
// PLI application registered.
class CallsOfARun : public VpiDesignRun {
 protected:
  // The right side of the top's continuous assignment.
  static vpiHandle CallOnTheRight() {
    vpiHandle it =
        vpi_iterate(vpiContAssign, vpi_handle_by_name(VpiText("top"), nullptr));
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

// §37.59: a call of a function is a func call...
TEST_F(CallsOfARun, AFunctionCallIsAFuncCallObject) {
  Run(kFunctionCall);
  EXPECT_EQ(vpi_get(vpiType, CallOnTheRight()), vpiFuncCall);
}

// ...and §37.42 reaches its arguments in order through vpiArgument.
TEST_F(CallsOfARun, AFunctionCallsArgumentIsTheNetPassed) {
  Run(kFunctionCall);
  EXPECT_EQ(NamesOf(vpiArgument, CallOnTheRight()),
            (std::vector<std::string>{"a"}));
}

// A call of a system function is a sys func call.
TEST_F(CallsOfARun, ASystemFunctionCallIsASysFuncCallObject) {
  Run("module top; wire [7:0] a; wire [31:0] y; assign y = $countones(a); "
      "endmodule\n");
  EXPECT_EQ(vpi_get(vpiType, CallOnTheRight()), vpiSysFuncCall);
}

// A func call standing as an expression reaches the function it calls, as a
// func call statement does (#5051).
TEST_F(CallsOfARun, AFunctionCallReachesItsFunction) {
  Run(kFunctionCall);
  vpiHandle f = Named(vpiTaskFunc, By("top"), "f");
  ASSERT_NE(f, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiFunction, CallOnTheRight())),
            VpiObjectOf(f));
}

// A func call a generate block's continuous assignment makes reaches the
// function of the block, which hides the module's of the same name (§23.9).
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
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiFunction, CallOnTheRight())),
            VpiObjectOf(f));
}

// What the calltf of $probe read each time it ran: the call that invoked it
// (detail 3), whether that call is user-defined (detail 5) and what it
// decompiles to, empty where it reports nothing (detail 9).
struct ProbeSighting {
  vpiHandle call;
  int user_defn;
  std::string decompile;
};
std::vector<ProbeSighting> g_probe_sightings;

PLI_INT32 ProbeCalltf(PLI_BYTE8* /*user_data*/) {
  vpiHandle call = vpi_handle(vpiSysTfCall, nullptr);
  const char* decompile = vpi_get_str(vpiDecompile, call);
  g_probe_sightings.push_back({call, vpi_get(vpiUserDefn, call),
                               decompile != nullptr ? decompile : ""});
  return 0;
}

// A design run with the system task $probe registered beside the fixture's
// own, whose call statements are read back from the model the run built.
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

  // The statement the first procedure `scope` declares runs.
  static vpiHandle BodyOf(const std::string& scope) {
    vpiHandle it = vpi_iterate(vpiProcess, By(scope));
    if (it == nullptr) return nullptr;
    return vpi_handle(vpiStmt, vpi_scan(it));
  }

  vpiHandle probe_ = nullptr;
};

// A system task call a procedure writes is a sys task call of the run, named
// after the system task, standing in the scope that writes it and running in
// its procedure (#5011).
TEST_F(CallStatementsOfARun, ASystemTaskCallIsAnObjectOfTheRun) {
  Run("module top; initial $display(\"hi\"); endmodule\n");
  vpiHandle call = BodyOf("top");
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(vpi_get(vpiType, call), vpiSysTaskCall);
  EXPECT_STREQ(vpi_get_str(vpiName, call), "$display");
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiScope, call)), VpiObjectOf(By("top")));
  EXPECT_NE(vpi_handle(vpiProcess, call), nullptr);
}

// A call of a task is a task call named after the task it calls (#5016)...
TEST_F(CallStatementsOfARun, ATaskCallIsAnObjectOfTheRun) {
  Run("module top; task t; endtask initial t; endmodule\n");
  vpiHandle call = BodyOf("top");
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(vpi_get(vpiType, call), vpiTaskCall);
  EXPECT_STREQ(vpi_get_str(vpiName, call), "t");
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiScope, call)), VpiObjectOf(By("top")));
}

// ...and a call of a void function written as a statement is a func call
// statement named after the function, the tf call class §37.60 draws in atomic
// stmt holding the function calls too (#5034).
TEST_F(CallStatementsOfARun, AFunctionCallStatementIsAFuncCall) {
  Run("module top; function void f(); endfunction initial f(); endmodule\n");
  vpiHandle call = BodyOf("top");
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(vpi_get(vpiType, call), vpiFuncCall);
  EXPECT_STREQ(vpi_get_str(vpiName, call), "f");
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiScope, call)), VpiObjectOf(By("top")));
  EXPECT_NE(vpi_handle(vpiProcess, call), nullptr);
}

// A built-in system function written as a statement is a sys func call that is
// not user-defined and reaches no user systf.
TEST_F(CallStatementsOfARun, ABuiltInSystemFunctionStatementIsASysFuncCall) {
  Run("module top; initial $random; endmodule\n");
  vpiHandle call = BodyOf("top");
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(vpi_get(vpiType, call), vpiSysFuncCall);
  EXPECT_STREQ(vpi_get_str(vpiName, call), "$random");
  EXPECT_EQ(vpi_get(vpiUserDefn, call), 0);
  EXPECT_EQ(vpi_handle(vpiUserSystf, call), nullptr);
}

// A call of a class's function method written as a statement is a method func
// call whose vpiPrefix is the class var it is applied to.
TEST_F(CallStatementsOfARun, AMethodFunctionCallStatementIsAMethodFuncCall) {
  Run("module top;\n"
      "  class C; function void go(); endfunction endclass\n"
      "  C obj = new;\n"
      "  initial obj.go();\n"
      "endmodule\n");
  vpiHandle call = BodyOf("top");
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(vpi_get(vpiType, call), vpiMethodFuncCall);
  EXPECT_STREQ(vpi_get_str(vpiName, call), "go");
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiPrefix, call)), "obj");
  EXPECT_EQ(vpi_get(vpiUserDefn, call), 1);
}

constexpr const char* kMethodTaskCall =
    "module top;\n"
    "  class C; task run(); endtask endclass\n"
    "  C obj = new;\n"
    "  initial obj.run();\n"
    "endmodule\n";

// A call of a class's task method is a method task call named after the
// method, whose vpiPrefix is the class var it is applied to (#5017, detail 2)
// and which, the class being the design's own, is user-defined.
TEST_F(CallStatementsOfARun, AMethodTaskCallIsAnObjectOfTheRun) {
  Run(kMethodTaskCall);
  vpiHandle call = BodyOf("top");
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(vpi_get(vpiType, call), vpiMethodTaskCall);
  EXPECT_STREQ(vpi_get_str(vpiName, call), "run");
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiPrefix, call)), "obj");
  EXPECT_EQ(vpi_get(vpiUserDefn, call), 1);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiScope, call)), VpiObjectOf(By("top")));
}

// A task call statement reaches the task it calls and a func call statement
// the function, each the declaration's object in the instance (#5024)...
TEST_F(CallStatementsOfARun, ACallStatementReachesItsDeclaration) {
  Run("module top; task t; endtask function void f(); endfunction\n"
      "  initial begin t; f(); end endmodule\n");
  vpiHandle task = Named(vpiTaskCall, BodyOf("top"), "t");
  vpiHandle func = Named(vpiFuncCall, BodyOf("top"), "f");
  ASSERT_NE(task, nullptr);
  ASSERT_NE(func, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiTask, task)),
            VpiObjectOf(Named(vpiTaskFunc, By("top"), "t")));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiFunction, func)),
            VpiObjectOf(Named(vpiTaskFunc, By("top"), "f")));
}

// ...a package's where the call names the package's subroutine (§26.3).
TEST_F(CallStatementsOfARun, APackageTaskCallReachesThePackageTask) {
  Run("package p; task t; endtask endpackage\n"
      "module top; initial p::t; endmodule\n");
  vpiHandle call = BodyOf("top");
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiTask, call)),
            VpiObjectOf(Named(vpiTaskFunc, By("p"), "t")));
}

// The method task call reaches the task method of the class it calls, and a
// method func call the function method, each the method its class defn holds
// (#5025)...
TEST_F(CallStatementsOfARun, AMethodCallReachesItsMethod) {
  Run("module top;\n"
      "  class C; task run(); endtask function void go(); endfunction\n"
      "  endclass\n"
      "  C obj = new;\n"
      "  initial begin obj.run(); obj.go(); end\n"
      "endmodule\n");
  vpiHandle defn = Named(vpiClassDefn, By("top"), "C");
  vpiHandle run = Named(vpiMethodTaskCall, BodyOf("top"), "run");
  vpiHandle go = Named(vpiMethodFuncCall, BodyOf("top"), "go");
  ASSERT_NE(run, nullptr);
  ASSERT_NE(go, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiTask, run)),
            VpiObjectOf(Named(vpiMethods, defn, "run")));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiFunction, go)),
            VpiObjectOf(Named(vpiMethods, defn, "go")));
}

// ...the base class's where the method is inherited (§8.13).
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

// A method called through a member chain, a.b.run(), is a method task call
// too, of the class the chain's last member holds a handle of, found through
// a property its class inherits (§8.13), and applied to that member: the class
// var b in the object a references now (detail 2, #5031).
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
  EXPECT_STREQ(vpi_get_str(vpiName, call), "run");
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

// A semaphore's get is a task of the built-in class (§15.3.3), so a call of it
// is a method task call that is not user-defined...
TEST_F(CallStatementsOfARun, ABuiltInClassTaskCallIsNotUserDefined) {
  Run("module top; semaphore s = new(1); initial s.get(1); endmodule\n");
  vpiHandle call = BodyOf("top");
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(vpi_get(vpiType, call), vpiMethodTaskCall);
  EXPECT_EQ(vpi_get(vpiUserDefn, call), 0);
}

// ...while its put is a function (§15.3.2), and a call of it a method func
// call that is not user-defined either (#5034).
TEST_F(CallStatementsOfARun, ABuiltInClassFunctionCallIsAMethodFuncCall) {
  Run("module top; semaphore s = new(1); initial s.put(1); endmodule\n");
  vpiHandle call = BodyOf("top");
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(vpi_get(vpiType, call), vpiMethodFuncCall);
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiPrefix, call)), "s");
  EXPECT_EQ(vpi_get(vpiUserDefn, call), 0);
}

// A call statement reaches the arguments it was written with, in order
// (#5018).
TEST_F(CallStatementsOfARun, ACallStatementReachesItsArguments) {
  Run("module top; int x; task t(input int a, input int b); endtask\n"
      "  initial begin $display(\"%d\", x); t(1, x); end endmodule\n");
  vpiHandle display = Named(vpiSysTaskCall, BodyOf("top"), "$display");
  vpiHandle task = Named(vpiTaskCall, BodyOf("top"), "t");
  ASSERT_NE(display, nullptr);
  ASSERT_NE(task, nullptr);
  vpiHandle it = vpi_iterate(vpiArgument, display);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(vpi_get(vpiType, vpi_scan(it)), vpiConstant);
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_scan(it)), "x");
  EXPECT_EQ(KindsOf(vpiArgument, task).size(), 2U);
}

// A func call passed as a call statement's argument reaches its function too
// (#5051).
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

// A call written in a generate block reaches the task of the block's own
// instance (#5053).
TEST_F(CallStatementsOfARun, AGenerateBlockCallReachesItsBlocksTask) {
  Run("module top; for (genvar i = 0; i < 2; i++) begin : g\n"
      "  task t(); endtask initial t; end endmodule\n");
  vpiHandle call = BodyOf("top.g[1]");
  ASSERT_NE(call, nullptr);
  vpiHandle task = Named(vpiTaskFunc, By("top.g[1]"), "t");
  ASSERT_NE(task, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiTask, call)), VpiObjectOf(task));
}

// The call a registered system task's calltf reaches is the model's object
// for the statement that invoked it (#5019), one per instance writing it.
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

// A call of a registered system task is user-defined, read from inside its
// calltf and off the model alike, and a call of a built-in one is not (#5020).
TEST_F(CallStatementsOfARun, ARegisteredSystemTaskCallIsUserDefined) {
  Run("module top; initial begin $probe; $display(\"hi\"); end endmodule\n");
  ASSERT_EQ(g_probe_sightings.size(), 1U);
  EXPECT_EQ(g_probe_sightings[0].user_defn, 1);
  EXPECT_EQ(
      vpi_get(vpiUserDefn, Named(vpiSysTaskCall, BodyOf("top"), "$probe")), 1);
  EXPECT_EQ(
      vpi_get(vpiUserDefn, Named(vpiSysTaskCall, BodyOf("top"), "$display")),
      0);
}

// A call of a registered system task reaches the systf its registration
// returned, and a call of a built-in one reaches none (#5022).
TEST_F(CallStatementsOfARun, ASystemTaskCallReachesItsUserSystf) {
  Run("module top; initial begin $probe; $display(\"hi\"); end endmodule\n");
  ASSERT_EQ(g_probe_sightings.size(), 1U);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiUserSystf, g_probe_sightings[0].call)),
            VpiObjectOf(probe_));
  EXPECT_EQ(vpi_handle(vpiUserSystf,
                       Named(vpiSysTaskCall, BodyOf("top"), "$display")),
            nullptr);
}

// The call the calltf of $peek last reached through vpiSysTfCall.
vpiHandle g_peek_call = nullptr;

PLI_INT32 PeekCalltf(PLI_BYTE8* /*user_data*/) {
  g_peek_call = vpi_handle(vpiSysTfCall, nullptr);
  return 0;
}

// A registered system function written as a statement is a sys func call that
// is user-defined, reaches the systf its registration returned, and is the very
// object its calltf reaches (#5034).
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

// A built-in system function written as a statement is no system task call:
// $random is a function of §20.14 and $urandom one of §18.13, while $cast,
// which §8.16 lets be called as a task, is a task where a statement calls it
// (#5027).
TEST_F(CallStatementsOfARun, ABuiltInSystemFunctionStatementIsNoSysTaskCall) {
  Run("module top; int a; real r = 2.0;\n"
      "  initial begin $random; $urandom; $cast(a, r); end endmodule\n");
  EXPECT_EQ(Named(vpiSysTaskCall, BodyOf("top"), "$random"), nullptr);
  EXPECT_EQ(Named(vpiSysTaskCall, BodyOf("top"), "$urandom"), nullptr);
  EXPECT_NE(Named(vpiSysTaskCall, BodyOf("top"), "$cast"), nullptr);
}

// An argument naming a scope that stands around the call is reached through
// vpiArgument like any other (#5028).
TEST_F(CallStatementsOfARun, AnArgumentNamingTheScopeAroundTheCallIsReached) {
  Run("module top; initial $printtimescale(top); endmodule\n");
  vpiHandle call = BodyOf("top");
  ASSERT_NE(call, nullptr);
  vpiHandle it = vpi_iterate(vpiArgument, call);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), VpiObjectOf(By("top")));
}

// A method task call on a class var a block declares is an object of the run,
// whose vpiPrefix is the block's variable rather than the module's variable
// of that name it shadows (#5029).
TEST_F(CallStatementsOfARun, AMethodTaskCallOnABlockVariableIsAnObject) {
  Run("module top;\n"
      "  class C; task run(); endtask endclass\n"
      "  int obj;\n"
      "  initial begin : b C obj; obj = new; obj.run(); end\n"
      "endmodule\n");
  vpiHandle call = Named(vpiMethodTaskCall, By("top.b"), "run");
  ASSERT_NE(call, nullptr);
  ASSERT_NE(By("top.b.obj"), nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiPrefix, call)),
            VpiObjectOf(By("top.b.obj")));
}

// A built-in method of a queue (§7.10.2), an associative array (§7.9), a
// string (§6.16) or an enum (§6.19.5) the module declares, called as a
// statement, is a method func call applied to the variable, and is not
// user-defined (#5035).
TEST_F(CallStatementsOfARun, ABuiltInMethodOfAModuleVariableIsAMethodFuncCall) {
  Run("module top; int q[$]; int aa[string]; string s = \"ab\";\n"
      "  typedef enum {A, B} e_t; e_t e;\n"
      "  initial begin q.push_back(1); aa.delete(); s.putc(0, \"c\");\n"
      "    e.next(); end\n"
      "endmodule\n");
  for (const auto& [method, holder] :
       std::vector<std::pair<std::string, std::string>>{{"push_back", "q"},
                                                        {"delete", "aa"},
                                                        {"putc", "s"},
                                                        {"next", "e"}}) {
    vpiHandle call = Named(vpiMethodFuncCall, BodyOf("top"), method);
    ASSERT_NE(call, nullptr) << method;
    EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiPrefix, call)),
                 holder.c_str());
    EXPECT_EQ(vpi_get(vpiUserDefn, call), 0) << method;
  }
}

// A block's dynamic array (§7.5) and fixed-size array take the methods of
// theirs and §7.12's alike, and the prefix is the block's variable.
TEST_F(CallStatementsOfARun, ABuiltInMethodOfABlockArrayIsAMethodFuncCall) {
  Run("module top; initial begin : b\n"
      "  int d[]; int f[2]; d.delete(); f.sort();\n"
      "end endmodule\n");
  vpiHandle del = Named(vpiMethodFuncCall, By("top.b"), "delete");
  vpiHandle sort = Named(vpiMethodFuncCall, By("top.b"), "sort");
  ASSERT_NE(del, nullptr);
  ASSERT_NE(sort, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiPrefix, del)),
            VpiObjectOf(By("top.b.d")));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiPrefix, sort)),
            VpiObjectOf(By("top.b.f")));
}

// §7.12.3's reduction methods apply to an associative array as to any other
// unpacked array.
TEST_F(CallStatementsOfARun, AnAssociativeArraysReductionIsAMethodFuncCall) {
  Run("module top; int aa[int]; initial aa.sum(); endmodule\n");
  vpiHandle call = BodyOf("top");
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(vpi_get(vpiType, call), vpiMethodFuncCall);
}

constexpr const char* kPackageTask = "package p; task t; endtask endpackage\n";

// A call of a task a package declares is a task call, whether the name was
// imported (#5030)...
TEST_F(CallStatementsOfARun, ACallOfAnImportedPackageTaskIsATaskCall) {
  Run(std::string(kPackageTask) +
      "module top; import p::*; initial t; endmodule\n");
  vpiHandle call = BodyOf("top");
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(vpi_get(vpiType, call), vpiTaskCall);
  EXPECT_STREQ(vpi_get_str(vpiName, call), "t");
}

// ...or written behind the package's name.
TEST_F(CallStatementsOfARun, AScopedCallOfAPackageTaskIsATaskCall) {
  Run(std::string(kPackageTask) + "module top; initial p::t; endmodule\n");
  vpiHandle call = BodyOf("top");
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(vpi_get(vpiType, call), vpiTaskCall);
  EXPECT_STREQ(vpi_get_str(vpiName, call), "t");
}

// A system task call statement decompiles to the call it makes, its arguments
// decompiled as any expression is (detail 9, #5021)...
TEST_F(CallStatementsOfARun, ASystemTaskCallStatementDecompilesToItsCall) {
  Run("module top; int a; initial $display(\"a=%0d\",  a+1); endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, BodyOf("top")),
               "$display(\"a=%0d\", a + 1)");
}

// ...one written with no arguments to its name alone...
TEST_F(CallStatementsOfARun, ASystemTaskCallWithNoArgumentsIsItsName) {
  Run("module top; initial $probe; endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, BodyOf("top")), "$probe");
}

// ...and the call a calltf reaches decompiles the same way, though the model
// holds no statement for a call a task's body writes.
TEST_F(CallStatementsOfARun, TheInvokingCallDecompilesToItsCall) {
  Run("module top; int a; task t; $probe(a*(a+1)); endtask\n"
      "  initial t; endmodule\n");
  ASSERT_EQ(g_probe_sightings.size(), 1U);
  EXPECT_EQ(g_probe_sightings[0].decompile, "$probe(a * (a + 1))");
}

// A name a call argument written in a block names is the block's declaration,
// which shadows the module's of that name (§23.9, #5062).
TEST_F(CallStatementsOfARun, AnArgumentNamesTheBlocksDeclaration) {
  Run("module top; int x;\n"
      "  initial begin : b int x; $display(x); end\n"
      "endmodule\n");
  vpiHandle call = Named(vpiSysTaskCall, By("top.b"), "$display");
  ASSERT_NE(call, nullptr);
  vpiHandle it = vpi_iterate(vpiArgument, call);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), VpiObjectOf(By("top.b.x")));
}

// Detail 6: the vpiUserSystf iteration passes over every object of the run
// that is no registered systf, a module among them.
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
