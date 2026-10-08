#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// §37.41 Task and function declaration: the object model diagram draws a "task
// func" object with "function" and "task" specializations. A function reaches
// its return-capture variable through vpiReturn and carries vpiSigned/vpiSize/
// vpiFuncType; the shared "task func" carries vpiMethod, vpiAccessType,
// vpiVisibility, vpiVirtual, vpiAutomatic, and the DPI properties vpiDPIPure,
// vpiDPIContext, vpiDPICStr, and vpiDPICIdentifier. The structural edges
// (vpiLeftRange/vpiRightRange, io decl, func/task call, class defn, vpiParent)
// are descriptive or generic; the lifetime property vpiAutomatic belongs to
// §37.3.7 and vpiVirtual is reported generically. The figure's vpiMethod and
// vpiSigned carry no numbered detail of their own but are Booleans §37.4.2
// reads with vpi_get(), so they are pinned below alongside the details. These
// tests pin the twelve numbered Details that constrain the model:
//   1-3) vpiReturn reaches a return-capture variable, always a var, that also
//        carries a user-defined return type for inspection;
//   4)   vpiVisibility falls back to vpiPublicVis;
//   5)   a tf inside a package or class is named with a "::" qualifier;
//   6-10) the DPI access type, pure, context, flavor, and C-identifier rules;
//   12)  vpiSize of a function tracks its vpiReturn variable, or 0 for void.
// Detail 11 (lifetime/memory allocation) is deferred to §37.3.7. The rules run
// through the production dispatch in vpi.cpp (vpi_handle/vpi_get/vpi_get_str)
// and the pure helpers it exposes.

// The fixture installs a context so the public vpi_get/vpi_get_str/vpi_handle
// entry points run their real dispatch.
class TaskFuncDeclaration : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// Details 1, 2, and 3: a function contains a return-capture object that shares
// its name, size, and type, and vpiReturn always reaches that var object - even
// for a plain scalar return. Details 1-3 collapse to one production branch: the
// relation hands back exactly the return variable. Reading vpiType off the
// reached handle is how a caller inspects the return type, including a
// user-defined one (detail 2); the rule §37.41 carries is that vpiReturn
// reaches the variable, which this exercises directly.
TEST_F(TaskFuncDeclaration, FunctionReturnReachesReturnCaptureVariable) {
  VpiObject ret;
  ret.type = vpiIntVar;  // detail 3: a var object, even for a simple return
  ret.name = "adder";
  ret.size = 32;

  VpiObject fn;
  fn.type = vpiFunction;
  fn.name = "adder";  // detail 1: same name as the function
  fn.size = 32;       // detail 1: same size as the function
  fn.return_var = &ret;

  vpiHandle reached = vpi_handle(vpiReturn, VpiHandleOf(&fn));
  ASSERT_EQ(VpiObjectOf(reached), &ret);
  // Detail 3: the reached object is a variable; detail 2: its type is readable
  // off the handle, which is how a user-defined return type is inspected.
  EXPECT_EQ(vpi_get(vpiType, reached), vpiIntVar);
  // Detail 1: it mirrors the function's name and size.
  EXPECT_EQ(std::string(vpi_get_str(vpiFullName, reached)), "adder");
  EXPECT_EQ(vpi_get(vpiSize, reached), 32);
}

// The vpiReturn relation is gated to a function reference. A task returns
// nothing, so even a stray return variable on a task is not reached; and
// because vpiReturn shares its constant value with vpiImmediateAssume, the gate
// keeps that other meaning from ever landing on this path.
TEST_F(TaskFuncDeclaration, ReturnRelationIsGatedToFunctions) {
  VpiObject ret;
  ret.type = vpiIntVar;

  VpiObject task;
  task.type = vpiTask;
  task.return_var = &ret;
  EXPECT_EQ(vpi_handle(vpiReturn, VpiHandleOf(&task)), nullptr);
}

// Detail 4: a task or function that is not a class member reports vpiPublicVis;
// a method reports its declared visibility, and a method that is neither local
// nor protected also reports vpiPublicVis.
TEST_F(TaskFuncDeclaration, VisibilityFallsBackToPublic) {
  // Not a class member -> public regardless of any declared value.
  EXPECT_EQ(VpiTaskFuncVisibility(/*is_class_member=*/false, vpiLocalVis),
            vpiPublicVis);
  // A local or protected method reports that declared visibility verbatim.
  EXPECT_EQ(VpiTaskFuncVisibility(/*is_class_member=*/true, vpiLocalVis),
            vpiLocalVis);
  EXPECT_EQ(VpiTaskFuncVisibility(/*is_class_member=*/true, vpiProtectedVis),
            vpiProtectedVis);
  // A member that is neither local nor protected reports public.
  EXPECT_EQ(VpiTaskFuncVisibility(/*is_class_member=*/true, vpiPublicVis),
            vpiPublicVis);
}

// Detail 5: a task or function declared inside a package or class is named with
// the enclosing scope's full name, the "::" separator, then the tf name. The
// qualified name flows through vpi_get_str(vpiFullName) for a function object.
TEST_F(TaskFuncDeclaration, FullNameQualifiedByPackageOrClass) {
  VpiObject pkg_fn;
  pkg_fn.type = vpiFunction;
  pkg_fn.name = "crc";
  pkg_fn.full_name = VpiPackageMemberFullName("pkg", "crc");
  EXPECT_EQ(std::string(vpi_get_str(vpiFullName, VpiHandleOf(&pkg_fn))),
            "pkg::crc");

  VpiObject class_fn;
  class_fn.type = vpiFunction;
  class_fn.name = "run";
  class_fn.full_name =
      VpiClassMemberFullName(/*is_static=*/true, "top", "Driver", "run");
  EXPECT_EQ(std::string(vpi_get_str(vpiFullName, VpiHandleOf(&class_fn))),
            "top.Driver::run");
}

// Detail 6: a DPI task or function reports vpiDPIExportAcc when it is an export
// and vpiDPIImportAcc when it is an import; a non-DPI tf is outside this rule.
TEST_F(TaskFuncDeclaration, DpiAccessTypeReportsImportAndExport) {
  VpiObject import_fn;
  import_fn.type = vpiFunction;
  import_fn.is_dpi = true;
  import_fn.dpi_export = false;
  EXPECT_EQ(vpi_get(vpiAccessType, VpiHandleOf(&import_fn)), vpiDPIImportAcc);

  VpiObject export_task;
  export_task.type = vpiTask;
  export_task.is_dpi = true;
  export_task.dpi_export = true;
  EXPECT_EQ(vpi_get(vpiAccessType, VpiHandleOf(&export_task)), vpiDPIExportAcc);

  // A plain function is not a DPI tf, so it falls through to its stored value.
  VpiObject plain_fn;
  plain_fn.type = vpiFunction;
  EXPECT_EQ(vpi_get(vpiAccessType, VpiHandleOf(&plain_fn)), 0);
}

// Detail 7: vpiDPIPure reports TRUE for a pure DPI import function and FALSE
// otherwise.
TEST_F(TaskFuncDeclaration, DpiPureReportedForPureImportFunction) {
  VpiObject pure_fn;
  pure_fn.type = vpiFunction;
  pure_fn.is_dpi = true;
  pure_fn.dpi_pure = true;
  EXPECT_EQ(vpi_get(vpiDPIPure, VpiHandleOf(&pure_fn)), 1);

  VpiObject impure_fn;
  impure_fn.type = vpiFunction;
  impure_fn.is_dpi = true;
  EXPECT_EQ(vpi_get(vpiDPIPure, VpiHandleOf(&impure_fn)), 0);
}

// Detail 8: vpiDPIContext reports TRUE for a context import DPI task or
// function and FALSE otherwise.
TEST_F(TaskFuncDeclaration, DpiContextReportedForContextImport) {
  VpiObject ctx_fn;
  ctx_fn.type = vpiFunction;
  ctx_fn.is_dpi = true;
  ctx_fn.dpi_context = true;
  EXPECT_EQ(vpi_get(vpiDPIContext, VpiHandleOf(&ctx_fn)), 1);

  VpiObject plain_fn;
  plain_fn.type = vpiFunction;
  plain_fn.is_dpi = true;
  EXPECT_EQ(vpi_get(vpiDPIContext, VpiHandleOf(&plain_fn)), 0);
}

// Detail 9: vpiDPICStr reports vpiDPIC for a "DPI-C" tf and vpiDPI for a "DPI"
// tf; a tf that is not a DPI tf carries no flavor.
TEST_F(TaskFuncDeclaration, DpiCStrDistinguishesDpiAndDpiC) {
  VpiObject dpi_c;
  dpi_c.type = vpiFunction;
  dpi_c.is_dpi = true;
  dpi_c.is_dpi_c = true;
  EXPECT_EQ(vpi_get(vpiDPICStr, VpiHandleOf(&dpi_c)), vpiDPIC);

  VpiObject dpi;
  dpi.type = vpiFunction;
  dpi.is_dpi = true;
  dpi.is_dpi_c = false;
  EXPECT_EQ(vpi_get(vpiDPICStr, VpiHandleOf(&dpi)), vpiDPI);

  VpiObject not_dpi;
  not_dpi.type = vpiFunction;
  EXPECT_EQ(vpi_get(vpiDPICStr, VpiHandleOf(&not_dpi)), 0);
}

// Detail 10: vpiDPICIdentifier reports the C linkage name of a DPI tf, and null
// when the object carries none.
TEST_F(TaskFuncDeclaration, DpiCIdentifierReportsCLinkageName) {
  VpiObject fn;
  fn.type = vpiFunction;
  fn.is_dpi = true;
  fn.dpi_c_identifier = "c_crc32";
  EXPECT_EQ(std::string(vpi_get_str(vpiDPICIdentifier, VpiHandleOf(&fn))),
            "c_crc32");

  VpiObject no_id;
  no_id.type = vpiFunction;
  EXPECT_EQ(vpi_get_str(vpiDPICIdentifier, VpiHandleOf(&no_id)), nullptr);
}

// Detail 12: vpiSize of a function equals the vpiSize of its return variable
// when that size is defined and determinable without evaluating the function; a
// void function reports 0; every other case is undefined (reported here as 0).
TEST_F(TaskFuncDeclaration, FunctionSizeTracksReturnVariableOrZeroForVoid) {
  // Defined and determinable -> the return variable's size.
  EXPECT_EQ(VpiFunctionSize(/*is_void_function=*/false,
                            /*return_size_defined=*/true, 16),
            16);
  // A void function -> 0.
  EXPECT_EQ(VpiFunctionSize(/*is_void_function=*/true,
                            /*return_size_defined=*/true, 16),
            0);
  // Not determinable without evaluating -> undefined, reported as 0.
  EXPECT_EQ(VpiFunctionSize(/*is_void_function=*/false,
                            /*return_size_defined=*/false, 16),
            0);
}

// The figure's "-> method / bool: vpiMethod" on the task func enclosure. Detail
// 4 says what a method is - a task or function that is a class member - and
// §37.31 detail 1 draws a class defn's vpiMethods relation to that enclosure.
// No case answered the property, so the figure's Boolean read nothing whatever
// the task or function was.
TEST_F(TaskFuncDeclaration, MethodIsTrueForATaskOrFunctionOfAClass) {
  VpiObject cls;
  cls.type = vpiClassDefn;

  VpiObject method;
  method.type = vpiFunction;
  method.parent = &cls;
  VpiObject task_method;
  task_method.type = vpiTask;
  task_method.parent = &cls;

  EXPECT_EQ(vpi_get(vpiMethod, VpiHandleOf(&method)), 1);
  EXPECT_EQ(vpi_get(vpiMethod, VpiHandleOf(&task_method)), 1);
}

// The same property on a task or function declared outside a class, and on an
// object that is not a task or function at all: neither is a method.
TEST_F(TaskFuncDeclaration, MethodIsFalseOutsideAClass) {
  VpiObject module;
  module.type = vpiModule;

  VpiObject fn;
  fn.type = vpiFunction;
  fn.parent = &module;

  EXPECT_EQ(vpi_get(vpiMethod, VpiHandleOf(&fn)), 0);
  EXPECT_EQ(vpi_get(vpiMethod, VpiHandleOf(&module)), 0);
}

// The figure's "-> sign / bool: vpiSigned" on the function. Detail 1 makes the
// function's return object share its type and detail 2 reaches it through
// vpiReturn, so the property is that object's signedness: §6.11 makes integer
// and the sized integral kinds signed and leaves the 4-state vector kinds
// unsigned.
TEST_F(TaskFuncDeclaration, SignedFollowsTheReturnVariablesType) {
  VpiObject signed_ret;
  signed_ret.type = vpiIntVar;
  VpiObject signed_fn;
  signed_fn.type = vpiFunction;
  signed_fn.return_var = &signed_ret;

  VpiObject unsigned_ret;
  unsigned_ret.type = vpiLogicVar;
  VpiObject unsigned_fn;
  unsigned_fn.type = vpiFunction;
  unsigned_fn.return_var = &unsigned_ret;

  EXPECT_EQ(vpi_get(vpiSigned, VpiHandleOf(&signed_fn)), 1);
  EXPECT_EQ(vpi_get(vpiSigned, VpiHandleOf(&unsigned_fn)), 0);
}

// A task returns nothing, so it has no return object to take a sign from, and
// neither has a void function (detail 12's vpiSize-0 case).
TEST_F(TaskFuncDeclaration, SignedIsFalseWithoutAReturnVariable) {
  VpiObject task;
  task.type = vpiTask;
  VpiObject void_fn;
  void_fn.type = vpiFunction;  // no return_var: a void function

  EXPECT_EQ(vpi_get(vpiSigned, VpiHandleOf(&task)), 0);
  EXPECT_EQ(vpi_get(vpiSigned, VpiHandleOf(&void_fn)), 0);
}

// A design run with a PLI application registered, whose tasks and functions
// are read back from the model the run built.
class TaskFuncsOfARun : public VpiDesignRun {};

// The integer a bound `relation`, vpiLeftRange or vpiRightRange, of `obj`
// reaches.
int BoundOf(int relation, vpiHandle obj) {
  s_vpi_value value = {};
  value.format = vpiIntVal;
  vpi_get_value(vpi_handle(relation, obj), &value);
  return value.value.integer;
}

// §37.41 (#4939): each task and function a module declares is a task or
// function of each of its instances, full-named under the instance...
TEST_F(TaskFuncsOfARun, AModuleDeclaresItsTasksAndFunctions) {
  Run("module top; function int f(); return 1; endfunction\n"
      "  task t(); endtask endmodule\n");
  EXPECT_EQ(NamesOf(vpiTaskFunc, By("top")),
            (std::vector<std::string>{"f", "t"}));
  vpiHandle f = Named(vpiTaskFunc, By("top"), "f");
  EXPECT_EQ(vpi_get(vpiType, f), vpiFunction);
  EXPECT_EQ(vpi_get(vpiType, Named(vpiTaskFunc, By("top"), "t")), vpiTask);
  EXPECT_STREQ(vpi_get_str(vpiFullName, f), "top.f");
}

// ...a package's is full-named through the package (detail 5)...
TEST_F(TaskFuncsOfARun, APackageSubroutineIsFullNamedThroughItsPackage) {
  Run("package pkg; function int g(); return 1; endfunction endpackage\n"
      "module top; endmodule\n");
  vpiHandle g = Named(vpiTaskFunc, By("pkg"), "g");
  ASSERT_NE(g, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, g), "pkg::g");
}

// ...and each reports its lifetime (detail 11), static unless declared
// automatic or declared in a scope whose default lifetime is automatic.
TEST_F(TaskFuncsOfARun, ASubroutineReportsItsLifetime) {
  Run("module top; function automatic int a(); return 1; endfunction\n"
      "  function int s(); return 1; endfunction endmodule\n"
      "package automatic pkg; task d(); endtask\n"
      "  task static k(); endtask endpackage\n");
  EXPECT_EQ(vpi_get(vpiAutomatic, Named(vpiTaskFunc, By("top"), "a")), 1);
  EXPECT_EQ(vpi_get(vpiAutomatic, Named(vpiTaskFunc, By("top"), "s")), 0);
  EXPECT_EQ(vpi_get(vpiAutomatic, Named(vpiTaskFunc, By("pkg"), "d")), 1);
  EXPECT_EQ(vpi_get(vpiAutomatic, Named(vpiTaskFunc, By("pkg"), "k")), 0);
}

// The figure's io decl relation (#5048): a task reaches an io decl per
// argument it declares, each with the direction written or the one the
// argument before it carries (§13.3), and reaching through vpiExpr the
// variable the argument declares in the task's scope (§37.13).
TEST_F(TaskFuncsOfARun, AnArgumentIsAnIoDeclOfItsTask) {
  Run("module top; task automatic t(input int a, output logic [3:0] b, c,\n"
      "  ref int d); endtask endmodule\n");
  vpiHandle t = Named(vpiTaskFunc, By("top"), "t");
  ASSERT_NE(t, nullptr);
  EXPECT_EQ(NamesOf(vpiIODecl, t),
            (std::vector<std::string>{"a", "b", "c", "d"}));
  EXPECT_EQ(vpi_get(vpiDirection, Named(vpiIODecl, t, "a")), vpiInput);
  EXPECT_EQ(vpi_get(vpiDirection, Named(vpiIODecl, t, "c")), vpiOutput);
  EXPECT_EQ(vpi_get(vpiDirection, Named(vpiIODecl, t, "d")), vpiRef);
  vpiHandle b = vpi_handle(vpiExpr, Named(vpiIODecl, t, "b"));
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(vpi_get(vpiType, b), vpiLogicVar);
  EXPECT_STREQ(vpi_get_str(vpiFullName, b), "top.t.b");
}

// Details 1 to 3 and 12 (#5049): a function holds its return in a variable
// of its own name and type, reached through vpiReturn, whose size is the
// function's, and the figure's vpiFuncType says what kind of value it
// returns...
TEST_F(TaskFuncsOfARun, AFunctionReturnsThroughAVariableOfItsOwnName) {
  Run("module top; function logic [7:0] f(); return 0; endfunction\n"
      "  function logic signed [3:0] s(); return 0; endfunction\n"
      "  function int i(); return 0; endfunction endmodule\n");
  vpiHandle f = Named(vpiTaskFunc, By("top"), "f");
  vpiHandle ret = vpi_handle(vpiReturn, f);
  ASSERT_NE(ret, nullptr);
  EXPECT_EQ(vpi_get(vpiType, ret), vpiLogicVar);
  EXPECT_STREQ(vpi_get_str(vpiName, ret), "f");
  EXPECT_EQ(vpi_get(vpiSize, ret), 8);
  EXPECT_EQ(vpi_get(vpiSize, f), 8);
  EXPECT_EQ(vpi_get(vpiFuncType, f), vpiSizedFunc);
  vpiHandle s = Named(vpiTaskFunc, By("top"), "s");
  EXPECT_EQ(vpi_get(vpiFuncType, s), vpiSizedSignedFunc);
  EXPECT_EQ(vpi_get(vpiSigned, s), 1);
  vpiHandle i = Named(vpiTaskFunc, By("top"), "i");
  EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiReturn, i)), vpiIntVar);
  EXPECT_EQ(vpi_get(vpiSize, i), 32);
}

// The figure's vpiLeftRange and vpiRightRange: a function reaches the bounds
// of the packed range its return type declares, as written, and none where
// the type declares no range.
TEST_F(TaskFuncsOfARun, AFunctionReachesTheBoundsOfItsReturnRange) {
  Run("module top; function logic [7:0] f(); return 0; endfunction\n"
      "  function logic [0:3] g(); return 0; endfunction\n"
      "  function int h(); return 0; endfunction endmodule\n");
  vpiHandle f = Named(vpiTaskFunc, By("top"), "f");
  ASSERT_NE(vpi_handle(vpiLeftRange, f), nullptr);
  EXPECT_EQ(BoundOf(vpiLeftRange, f), 7);
  EXPECT_EQ(BoundOf(vpiRightRange, f), 0);
  vpiHandle g = Named(vpiTaskFunc, By("top"), "g");
  EXPECT_EQ(BoundOf(vpiLeftRange, g), 0);
  EXPECT_EQ(BoundOf(vpiRightRange, g), 3);
  vpiHandle h = Named(vpiTaskFunc, By("top"), "h");
  EXPECT_EQ(vpi_handle(vpiLeftRange, h), nullptr);
  EXPECT_EQ(vpi_handle(vpiRightRange, h), nullptr);
}

// §37.17 details 4 and 6 (#5056): the return variable, an argument's variable
// and a body's variable each reach the bounds of their leftmost dimension, an
// unpacked one before a packed one, and a range object per dimension; a
// variable whose type writes no range reaches neither.
TEST_F(TaskFuncsOfARun, ATaskFuncsVariablesReachTheirRanges) {
  Run("module top; function logic [7:0] f(input logic [3:0] a);\n"
      "  logic [0:5] v; logic [1:0] w [2:9]; int n; return 0; endfunction\n"
      "endmodule\n");
  vpiHandle f = Named(vpiTaskFunc, By("top"), "f");
  vpiHandle ret = vpi_handle(vpiReturn, f);
  ASSERT_NE(vpi_handle(vpiLeftRange, ret), nullptr);
  EXPECT_EQ(BoundOf(vpiLeftRange, ret), 7);
  EXPECT_EQ(BoundOf(vpiRightRange, ret), 0);
  vpiHandle a = vpi_handle(vpiExpr, Named(vpiIODecl, f, "a"));
  EXPECT_EQ(BoundOf(vpiLeftRange, a), 3);
  EXPECT_EQ(BoundOf(vpiRightRange, a), 0);
  vpiHandle v = Named(vpiVariables, f, "v");
  EXPECT_EQ(BoundOf(vpiLeftRange, v), 0);
  EXPECT_EQ(BoundOf(vpiRightRange, v), 5);
  vpiHandle w = Named(vpiVariables, f, "w");
  EXPECT_EQ(BoundOf(vpiLeftRange, w), 2);
  EXPECT_EQ(BoundOf(vpiRightRange, w), 9);
  vpiHandle ranges = vpi_iterate(vpiRange, w);
  ASSERT_NE(ranges, nullptr);
  EXPECT_EQ(vpi_get(vpiSize, vpi_scan(ranges)), 8);
  vpi_free_object(ranges);
  vpiHandle n = Named(vpiVariables, f, "n");
  EXPECT_EQ(vpi_iterate(vpiRange, n), nullptr);
  EXPECT_EQ(vpi_handle(vpiLeftRange, n), nullptr);
}

// ...while a void function returns nothing and has size 0, and a function of
// an integer, a real or a time returns the kind of value its type names.
TEST_F(TaskFuncsOfARun, AVoidFunctionHasNoReturnVariable) {
  Run("module top; function void v(); endfunction\n"
      "  function integer n(); return 0; endfunction\n"
      "  function real r(); return 0; endfunction\n"
      "  function time t(); return 0; endfunction endmodule\n");
  vpiHandle v = Named(vpiTaskFunc, By("top"), "v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(vpi_handle(vpiReturn, v), nullptr);
  EXPECT_EQ(vpi_get(vpiSize, v), 0);
  EXPECT_EQ(vpi_get(vpiFuncType, Named(vpiTaskFunc, By("top"), "n")),
            vpiIntFunc);
  EXPECT_EQ(vpi_get(vpiFuncType, Named(vpiTaskFunc, By("top"), "r")),
            vpiRealFunc);
  EXPECT_EQ(vpi_get(vpiFuncType, Named(vpiTaskFunc, By("top"), "t")),
            vpiTimeFunc);
}

// A task or function is a scope (#5050), reaching the variables its body
// declares, each automatic as written or as the subroutine's lifetime makes it
// (§13.3.1, §13.4.2).
TEST_F(TaskFuncsOfARun, AFunctionDeclaresTheVariablesItsBodyDeclares) {
  Run("module top; function int f(); int tmp; automatic int a;\n"
      "  return tmp; endfunction\n"
      "  function automatic int g(); int loc; static int keep;\n"
      "  return loc; endfunction endmodule\n");
  vpiHandle f = Named(vpiTaskFunc, By("top"), "f");
  vpiHandle g = Named(vpiTaskFunc, By("top"), "g");
  EXPECT_EQ(NamesOf(vpiVariables, f), (std::vector<std::string>{"a", "tmp"}));
  vpiHandle tmp = Named(vpiVariables, f, "tmp");
  EXPECT_STREQ(vpi_get_str(vpiFullName, tmp), "top.f.tmp");
  EXPECT_EQ(vpi_get(vpiAutomatic, tmp), 0);
  EXPECT_EQ(vpi_get(vpiAutomatic, Named(vpiVariables, f, "a")), 1);
  EXPECT_EQ(vpi_get(vpiAutomatic, Named(vpiVariables, g, "loc")), 1);
  EXPECT_EQ(vpi_get(vpiAutomatic, Named(vpiVariables, g, "keep")), 0);
}

// A task a generate block declares is a task of the block's instance, one per
// instance of a loop generate's block, and none of the module's (#5053).
TEST_F(TaskFuncsOfARun, AGenerateBlockTaskIsATaskOfTheBlock) {
  Run("module top; for (genvar i = 0; i < 2; i++) begin : g\n"
      "  task t(); endtask end endmodule\n");
  EXPECT_TRUE(NamesOf(vpiTaskFunc, By("top")).empty());
  vpiHandle t0 = Named(vpiTaskFunc, By("top.g[0]"), "t");
  vpiHandle t1 = Named(vpiTaskFunc, By("top.g[1]"), "t");
  ASSERT_NE(t0, nullptr);
  ASSERT_NE(t1, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, t1), "top.g[1].t");
  EXPECT_NE(VpiObjectOf(t0), VpiObjectOf(t1));
}

// §37.41 detail 4 and (figure): no object is no method, nor is a function with
// no parent; and a function returning a byte, short int, long int or integer
// is signed (§6.11), where no object is not.
TEST(TaskFuncModel, MethodAndSignOfLooseObjects) {
  EXPECT_FALSE(VpiTaskFuncIsMethod(nullptr));
  VpiObject loose;
  loose.type = vpiFunction;
  EXPECT_FALSE(VpiTaskFuncIsMethod(&loose));
  EXPECT_FALSE(VpiFunctionIsSigned(nullptr));
  for (int type : {vpiByteVar, vpiShortIntVar, vpiLongIntVar, vpiIntegerVar}) {
    VpiObject ret;
    ret.type = type;
    VpiObject function;
    function.type = vpiFunction;
    function.return_var = &ret;
    EXPECT_TRUE(VpiFunctionIsSigned(&function)) << type;
  }
}

}  // namespace
}  // namespace delta
