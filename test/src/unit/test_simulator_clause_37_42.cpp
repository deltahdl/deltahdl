#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

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

  EXPECT_EQ(vpi_handle(vpiPrefix, &send), &packet);

  // A plain function call is not a method call: vpiPrefix does not apply, even
  // when a prefix object happens to be set, so the gating reports NULL.
  VpiObject func;
  func.type = vpiFuncCall;
  func.tf_prefix = &packet;
  EXPECT_EQ(vpi_handle(vpiPrefix, &func), nullptr);
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
  EXPECT_EQ(vpi_handle(vpiWith, &randomize), &with_expr);

  // An ordinary method call does not accept a with clause: the relation is
  // unavailable, so vpiWith reports NULL despite the attached object.
  VpiObject ordinary;
  ordinary.type = vpiMethodFuncCall;
  ordinary.tf_with = &with_expr;
  ordinary.tf_with_method = false;
  EXPECT_EQ(vpi_handle(vpiWith, &ordinary), nullptr);
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
  EXPECT_EQ(vpi_handle(vpiWith, &randomize), &with_constraint);
}

// Detail 3: the system task or function that invoked the application is reached
// with vpi_handle(vpiSysTfCall, NULL).
TEST_F(TaskFuncCall, InvokingSystemTfCallReachedWithNullRef) {
  VpiObject call;
  call.type = vpiSysTaskCall;
  ctx_.SetCurrentSystfCall(&call);

  EXPECT_EQ(vpi_handle(vpiSysTfCall, nullptr), &call);

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
  task.tfname = "$as_task";
  vpiHandle task_h = vpi_register_systf(&task);
  ASSERT_NE(task_h, nullptr);

  s_vpi_systf_data func = {};
  func.type = vpiSysFunc;
  func.tfname = "$as_func";
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
  EXPECT_EQ(vpi_get(vpiType, &empty), vpiOperation);
  EXPECT_EQ(vpi_get(vpiOpType, &empty), vpiNullOp);

  VpiObject null_arg;
  VpiMakeNullArgument(&null_arg);
  EXPECT_EQ(vpi_get(vpiType, &null_arg), vpiConstant);
  EXPECT_EQ(vpi_get(vpiConstType, &null_arg), vpiNullConst);

  // The vpiArgument relation reaches exprs, an interface expr, a scope, a
  // primitive, and named events; a statement or a module is not an argument.
  EXPECT_TRUE(VpiIsTfCallArgumentType(vpiOperation));  // an expr kind
  EXPECT_TRUE(VpiIsTfCallArgumentType(vpiInterface));  // an interface expr kind
  EXPECT_TRUE(VpiIsTfCallArgumentType(vpiScope));
  EXPECT_TRUE(VpiIsTfCallArgumentType(vpiGate));  // a primitive
  EXPECT_TRUE(VpiIsTfCallArgumentType(vpiNamedEvent));
  EXPECT_TRUE(VpiIsTfCallArgumentType(vpiNamedEventArray));
  EXPECT_FALSE(VpiIsTfCallArgumentType(vpiIf));  // a statement
  EXPECT_FALSE(VpiIsTfCallArgumentType(vpiModule));
}

// Detail 10: iterating a protected object's relationships is normally an error,
// but a protected system task or function call still allows iteration over its
// vpiArgument relation. The argument iteration collects only the call's
// argument objects (excluding a non-argument child), while any other relation
// on the same protected call is still refused.
TEST_F(TaskFuncCall, ProtectedCallStillIteratesArguments) {
  VpiObject arg0;
  arg0.type = vpiOperation;  // an argument expression
  VpiObject arg1;
  arg1.type = vpiNamedEvent;  // a named-event argument
  VpiObject not_arg;
  not_arg.type = vpiTypespec;  // a child that is not a call argument

  VpiObject call;
  call.type = vpiSysTaskCall;
  call.is_protected = true;
  call.children = {&arg0, &not_arg, &arg1};

  vpiHandle it = vpi_iterate(vpiArgument, &call);
  ASSERT_NE(it, nullptr);
  int count = 0;
  bool saw_arg0 = false;
  bool saw_arg1 = false;
  while (vpiHandle h = vpi_scan(it)) {
    ++count;
    if (h == &arg0) saw_arg0 = true;
    if (h == &arg1) saw_arg1 = true;
  }
  EXPECT_EQ(count, 2);  // the non-argument child is excluded
  EXPECT_TRUE(saw_arg0);
  EXPECT_TRUE(saw_arg1);

  // Iterating any other relation of the protected call is still an error - no
  // iterator is produced.
  EXPECT_EQ(vpi_iterate(vpiTypespec, &call), nullptr);
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
  EXPECT_EQ(vpi_handle(vpiFunction, &builtin_fn), nullptr);

  // A user-defined method func call reaches its function object.
  VpiObject user_fn;
  user_fn.type = vpiMethodFuncCall;
  user_fn.builtin_method = false;
  VpiObject user_fn_obj;
  user_fn_obj.type = vpiFunction;
  user_fn.children = {&user_fn_obj};
  EXPECT_EQ(vpi_handle(vpiFunction, &user_fn), &user_fn_obj);

  // The same rule governs a built-in method task call through vpiTask.
  VpiObject builtin_task;
  builtin_task.type = vpiMethodTaskCall;
  builtin_task.builtin_method = true;
  VpiObject task_obj;
  task_obj.type = vpiTask;
  builtin_task.children = {&task_obj};
  EXPECT_EQ(vpi_handle(vpiTask, &builtin_task), nullptr);
}

// Diagram property (-> type): a func call and a sys func call report their
// function return-type class through vpiFuncType (vpiSysFuncType is the same
// constant). The stored type code is handed straight back; a call that carries
// no type - and an object that is not a function call - reports zero.
TEST_F(TaskFuncCall, FuncTypeReportedForFunctionCalls) {
  VpiObject func;
  func.type = vpiFuncCall;
  func.func_type = vpiIntFunc;
  EXPECT_EQ(vpi_get(vpiFuncType, &func), vpiIntFunc);

  // A system function call reports through the same property (vpiSysFuncType is
  // #defined equal to vpiFuncType).
  VpiObject sys_func;
  sys_func.type = vpiSysFuncCall;
  sys_func.func_type = vpiRealFunc;
  EXPECT_EQ(vpi_get(vpiSysFuncType, &sys_func), vpiRealFunc);

  // A call that stored no function type reports zero.
  VpiObject untyped;
  untyped.type = vpiFuncCall;
  EXPECT_EQ(vpi_get(vpiFuncType, &untyped), 0);
}

// Detail 5 (property): a method call and a system task/function call report
// whether they are user-defined through the vpiUserDefn Boolean property; a
// call not so flagged reports false.
TEST_F(TaskFuncCall, UserDefnReportedForCalls) {
  VpiObject user_sys;
  user_sys.type = vpiSysTaskCall;
  user_sys.user_defined = true;
  EXPECT_EQ(vpi_get(vpiUserDefn, &user_sys), 1);

  VpiObject builtin_sys;
  builtin_sys.type = vpiSysFuncCall;
  builtin_sys.user_defined = false;
  EXPECT_EQ(vpi_get(vpiUserDefn, &builtin_sys), 0);
}

// Detail 5 / figure (method-call position): vpiUserDefn is drawn on the method
// calls as well as the system calls. A method func or task call reports its
// user-defined flag through the same property; the accepting and negative forms
// are both observed on a method call.
TEST_F(TaskFuncCall, UserDefnReportedForMethodCalls) {
  VpiObject user_method;
  user_method.type = vpiMethodFuncCall;
  user_method.user_defined = true;
  EXPECT_EQ(vpi_get(vpiUserDefn, &user_method), 1);

  VpiObject builtin_method;
  builtin_method.type = vpiMethodTaskCall;
  builtin_method.user_defined = false;
  EXPECT_EQ(vpi_get(vpiUserDefn, &builtin_method), 0);
}

// Detail 9: a system task or function call reports, through the vpiDecompile
// string property, a functionally equivalent call to the source text. A call
// that carries no decompiled form, and an object that is not a system call,
// report null rather than an empty string.
TEST_F(TaskFuncCall, DecompileReportedForSystemCalls) {
  VpiObject call;
  call.type = vpiSysTaskCall;
  call.decompile = "$strobe(a, b)";
  EXPECT_STREQ(vpi_get_str(vpiDecompile, &call), "$strobe(a, b)");

  // A system call with no stored decompiled form reports null.
  VpiObject bare;
  bare.type = vpiSysFuncCall;
  EXPECT_EQ(vpi_get_str(vpiDecompile, &bare), nullptr);

  // The property is drawn only on system calls: an ordinary method call reports
  // null even when a decompiled string is attached.
  VpiObject method;
  method.type = vpiMethodTaskCall;
  method.decompile = "packet.send()";
  EXPECT_EQ(vpi_get_str(vpiDecompile, &method), nullptr);
}

}  // namespace
}  // namespace delta
