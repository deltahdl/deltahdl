#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class TaskFuncDeclaration : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

TEST_F(TaskFuncDeclaration, FunctionReturnReachesReturnCaptureVariable) {
  VpiObject ret;
  ret.type = vpiIntVar;
  ret.name = "adder";
  ret.size = 32;

  VpiObject fn;
  fn.type = vpiFunction;
  fn.name = "adder";
  fn.size = 32;
  fn.return_var = &ret;

  vpiHandle reached = vpi_handle(vpiReturn, VpiHandleOf(&fn));
  ASSERT_EQ(VpiObjectOf(reached), &ret);
  EXPECT_EQ(vpi_get(vpiType, reached), vpiIntVar);
  EXPECT_EQ(std::string(vpi_get_str(vpiFullName, reached)), "adder");
  EXPECT_EQ(vpi_get(vpiSize, reached), 32);
}

TEST_F(TaskFuncDeclaration, ReturnRelationIsGatedToFunctions) {
  VpiObject ret;
  ret.type = vpiIntVar;

  VpiObject task;
  task.type = vpiTask;
  task.return_var = &ret;
  EXPECT_EQ(vpi_handle(vpiReturn, VpiHandleOf(&task)), nullptr);
}

TEST_F(TaskFuncDeclaration, VisibilityFallsBackToPublic) {
  EXPECT_EQ(VpiTaskFuncVisibility(false, vpiLocalVis), vpiPublicVis);
  EXPECT_EQ(VpiTaskFuncVisibility(true, vpiLocalVis), vpiLocalVis);
  EXPECT_EQ(VpiTaskFuncVisibility(true, vpiProtectedVis), vpiProtectedVis);
  EXPECT_EQ(VpiTaskFuncVisibility(true, vpiPublicVis), vpiPublicVis);
}

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
  class_fn.full_name = VpiClassMemberFullName(true, "top", "Driver", "run");
  EXPECT_EQ(std::string(vpi_get_str(vpiFullName, VpiHandleOf(&class_fn))),
            "top.Driver::run");
}

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

  VpiObject plain_fn;
  plain_fn.type = vpiFunction;
  EXPECT_EQ(vpi_get(vpiAccessType, VpiHandleOf(&plain_fn)), 0);
}

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

TEST_F(TaskFuncDeclaration, FunctionSizeTracksReturnVariableOrZeroForVoid) {
  EXPECT_EQ(VpiFunctionSize(false, true, 16), 16);
  EXPECT_EQ(VpiFunctionSize(true, true, 16), 0);
  EXPECT_EQ(VpiFunctionSize(false, false, 16), 0);
}

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

TEST_F(TaskFuncDeclaration, MethodIsFalseOutsideAClass) {
  VpiObject module;
  module.type = vpiModule;

  VpiObject fn;
  fn.type = vpiFunction;
  fn.parent = &module;

  EXPECT_EQ(vpi_get(vpiMethod, VpiHandleOf(&fn)), 0);
  EXPECT_EQ(vpi_get(vpiMethod, VpiHandleOf(&module)), 0);
}

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

TEST_F(TaskFuncDeclaration, SignedIsFalseWithoutAReturnVariable) {
  VpiObject task;
  task.type = vpiTask;
  VpiObject void_fn;
  void_fn.type = vpiFunction;

  EXPECT_EQ(vpi_get(vpiSigned, VpiHandleOf(&task)), 0);
  EXPECT_EQ(vpi_get(vpiSigned, VpiHandleOf(&void_fn)), 0);
}

class TaskFuncsOfARun : public VpiDesignRun {};

int BoundOf(int relation, vpiHandle obj) {
  s_vpi_value value = {};
  value.format = vpiIntVal;
  vpi_get_value(vpi_handle(relation, obj), &value);
  return value.value.integer;
}

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

TEST_F(TaskFuncsOfARun, APackageSubroutineIsFullNamedThroughItsPackage) {
  Run("package pkg; function int g(); return 1; endfunction endpackage\n"
      "module top; endmodule\n");
  vpiHandle g = Named(vpiTaskFunc, By("pkg"), "g");
  ASSERT_NE(g, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, g), "pkg::g");
}

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

TEST_F(TaskFuncsOfARun, EachKindOfReturnHasItsFuncType) {
  Run("module top; function shortreal sr(); return 0; endfunction\n"
      "  function realtime rt(); return 0; endfunction\n"
      "  function [3:0] im(); return 0; endfunction\n"
      "  function reg rg(); return 0; endfunction\n"
      "  function bit bt(); return 0; endfunction\n"
      "  function byte by(); return 0; endfunction\n"
      "  function shortint si(); return 0; endfunction\n"
      "  function longint li(); return 0; endfunction\n"
      "  function string st(); return \"\"; endfunction endmodule\n");
  const auto kFuncType = [](const char* name) {
    return vpi_get(vpiFuncType, Named(vpiTaskFunc, By("top"), name));
  };
  EXPECT_EQ(kFuncType("sr"), vpiRealFunc);
  EXPECT_EQ(kFuncType("rt"), vpiRealFunc);
  EXPECT_EQ(kFuncType("im"), vpiSizedFunc);
  EXPECT_EQ(kFuncType("rg"), vpiSizedFunc);
  EXPECT_EQ(kFuncType("bt"), vpiSizedFunc);
  EXPECT_EQ(kFuncType("by"), vpiSizedSignedFunc);
  EXPECT_EQ(kFuncType("si"), vpiSizedSignedFunc);
  EXPECT_EQ(kFuncType("li"), vpiSizedSignedFunc);
  EXPECT_EQ(kFuncType("st"), vpiOtherFunc);
}

TEST_F(TaskFuncsOfARun, AnInoutArgumentIsAnInoutIoDecl) {
  Run("module top; task t(inout int x); endtask endmodule\n");
  vpiHandle t = Named(vpiTaskFunc, By("top"), "t");
  EXPECT_EQ(vpi_get(vpiDirection, Named(vpiIODecl, t, "x")), vpiInout);
}

TEST_F(TaskFuncsOfARun, AVariableOfANamedTypeHasTheTypesKind) {
  Run("module top; typedef enum {A, B} e_t;\n"
      "  function e_t f(e_t x); return x; endfunction endmodule\n");
  vpiHandle f = Named(vpiTaskFunc, By("top"), "f");
  EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiReturn, f)), vpiEnumVar);
  EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiExpr, Named(vpiIODecl, f, "x"))),
            vpiEnumVar);
}

TEST_F(TaskFuncsOfARun, AFunctionOfAnArrayTypeReturnsThroughAnArrayVar) {
  Run("module top; typedef int arr_t [2];\n"
      "  function arr_t f(); return '{1, 2}; endfunction endmodule\n");
  vpiHandle f = Named(vpiTaskFunc, By("top"), "f");
  EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiReturn, f)), vpiArrayVar);
}

int VariableKindOf(vpiHandle tf, std::string_view name) {
  for (const VpiObject* child : VpiObjectOf(tf)->children) {
    if (child->name == name && child->type != vpiIODecl) return child->type;
  }
  return 0;
}

TEST_F(TaskFuncsOfARun, ABodysEventArrayIsANamedEventArray) {
  Run("module top; task t(); event e [2]; int n [2];\n"
      "  localparam int P = 1; endtask endmodule\n");
  vpiHandle t = Named(vpiTaskFunc, By("top"), "t");
  ASSERT_NE(t, nullptr);
  EXPECT_EQ(VariableKindOf(t, "e"), vpiNamedEventArray);
  EXPECT_EQ(VariableKindOf(t, "n"), vpiArrayVar);
  EXPECT_EQ(VariableKindOf(t, "P"), 0);
}

TEST_F(TaskFuncsOfARun, APackageFunctionsNamedTypesHaveTheirKinds) {
  Run("package p; typedef int t; class C; endclass\n"
      "  function t f(t a); C h; return a; endfunction endpackage\n"
      "module top; endmodule\n");
  vpiHandle f = Named(vpiTaskFunc, By("p"), "f");
  ASSERT_NE(f, nullptr);
  EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiReturn, f)), vpiIntVar);
  EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiExpr, Named(vpiIODecl, f, "a"))),
            vpiIntVar);
  EXPECT_EQ(VariableKindOf(f, "h"), vpiClassVar);
}

TEST_F(TaskFuncsOfARun, AUnitFunctionsNamedTypesHaveTheirKinds) {
  Run("int n = 0; typedef enum {A, B} e_t; class K; endclass\n"
      "function e_t g(e_t x); K k; return x; endfunction\n"
      "module top; endmodule\n");
  vpiHandle it = vpi_iterate(vpiPackage, nullptr);
  ASSERT_NE(it, nullptr);
  vpiHandle g = Named(vpiTaskFunc, vpi_scan(it), "g");
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiReturn, g)), vpiEnumVar);
  EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiExpr, Named(vpiIODecl, g, "x"))),
            vpiEnumVar);
  EXPECT_EQ(VariableKindOf(g, "k"), vpiClassVar);
}

TEST_F(TaskFuncsOfARun, AGenerateBlockTaskTakesItsModulesLifetime) {
  Run("module automatic top; if (1) begin : g task t(); endtask\n"
      "  task static s(); endtask end endmodule\n");
  vpiHandle t = Named(vpiTaskFunc, By("top.g"), "t");
  vpiHandle s = Named(vpiTaskFunc, By("top.g"), "s");
  ASSERT_NE(t, nullptr);
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(vpi_get(vpiAutomatic, t), 1);
  EXPECT_EQ(vpi_get(vpiAutomatic, s), 0);
}

TEST_F(TaskFuncsOfARun, ACompilationUnitFunctionIsTheUnits) {
  Run("int g = 3;\n"
      "function int f(); return g; endfunction\n"
      "module top; endmodule\n");
  vpiHandle it = vpi_iterate(vpiPackage, nullptr);
  ASSERT_NE(it, nullptr);
  vpiHandle unit = vpi_scan(it);
  vpiHandle f = Named(vpiTaskFunc, unit, "f");
  ASSERT_NE(f, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, f), "$unit::f");
  EXPECT_TRUE(VpiObjectOf(f)->in_compilation_unit);
  EXPECT_EQ(vpi_handle_by_name(VpiText("f"), unit), nullptr);
}

TEST_F(TaskFuncsOfARun, ADpiImportIsATaskOrFunctionOfItsModule) {
  Run("module top;\n"
      "  import \"DPI-C\" function int c_f(input int a);\n"
      "  import \"DPI-C\" task c_t();\n"
      "  initial if (0) begin : b void'(c_f(1)); end\n"
      "endmodule\n");
  vpiHandle f = Named(vpiTaskFunc, By("top"), "c_f");
  ASSERT_NE(f, nullptr);
  EXPECT_EQ(vpi_get(vpiType, f), vpiFunction);
  EXPECT_STREQ(vpi_get_str(vpiFullName, f), "top.c_f");
  EXPECT_EQ(NamesOf(vpiIODecl, f), (std::vector<std::string>{"a"}));
  EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiReturn, f)), vpiIntVar);
  EXPECT_EQ(vpi_get(vpiSize, f), 32);
  vpiHandle t = Named(vpiTaskFunc, By("top"), "c_t");
  ASSERT_NE(t, nullptr);
  EXPECT_EQ(vpi_get(vpiType, t), vpiTask);
  EXPECT_EQ(vpi_handle(vpiReturn, t), nullptr);
  const std::vector<vpiHandle> kCalls = ObjectsOf(vpiFuncCall, By("top.b"));
  ASSERT_EQ(kCalls.size(), 1U);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiFunction, kCalls[0])), VpiObjectOf(f));
}

TEST_F(TaskFuncsOfARun, ADpiImportOfAPackageOrTheUnitIsTheirs) {
  Run("int n = 0;\n"
      "import \"DPI-C\" function int u_f();\n"
      "package p; import \"DPI-C\" function int p_f(); endpackage\n"
      "module top; initial if (0) begin : b void'(u_f()); end endmodule\n");
  vpiHandle p_f = Named(vpiTaskFunc, By("p"), "p_f");
  ASSERT_NE(p_f, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, p_f), "p::p_f");
  vpiHandle unit = Named(vpiPackage, nullptr, "$unit");
  ASSERT_NE(unit, nullptr);
  vpiHandle u_f = Named(vpiTaskFunc, unit, "u_f");
  ASSERT_NE(u_f, nullptr);
  EXPECT_EQ(vpi_get(vpiAccessType, u_f), vpiDPIImportAcc);
  const std::vector<vpiHandle> kCalls = ObjectsOf(vpiFuncCall, By("top.b"));
  ASSERT_EQ(kCalls.size(), 1U);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiFunction, kCalls[0])), VpiObjectOf(u_f));
}

TEST_F(TaskFuncsOfARun, ADpiTaskOrFunctionReportsItsDpiProperties) {
  Run("module top;\n"
      "  import \"DPI-C\" pure function int p_f(int a);\n"
      "  import \"DPI-C\" context c_name = function int c_f();\n"
      "  import \"DPI\" task d_t();\n"
      "  function int e_f(); return 1; endfunction\n"
      "  export \"DPI-C\" e_name = function e_f;\n"
      "  function int s_f(); return 1; endfunction\n"
      "endmodule\n");
  vpiHandle p_f = Named(vpiTaskFunc, By("top"), "p_f");
  vpiHandle c_f = Named(vpiTaskFunc, By("top"), "c_f");
  vpiHandle d_t = Named(vpiTaskFunc, By("top"), "d_t");
  vpiHandle e_f = Named(vpiTaskFunc, By("top"), "e_f");
  vpiHandle s_f = Named(vpiTaskFunc, By("top"), "s_f");
  ASSERT_NE(p_f, nullptr);
  ASSERT_NE(c_f, nullptr);
  ASSERT_NE(d_t, nullptr);
  EXPECT_EQ(vpi_get(vpiAccessType, p_f), vpiDPIImportAcc);
  EXPECT_EQ(vpi_get(vpiDPIPure, p_f), 1);
  EXPECT_EQ(vpi_get(vpiDPIContext, p_f), 0);
  EXPECT_EQ(vpi_get(vpiDPICStr, p_f), vpiDPIC);
  EXPECT_STREQ(vpi_get_str(vpiDPICIdentifier, p_f), "p_f");
  EXPECT_EQ(vpi_get(vpiDPIPure, c_f), 0);
  EXPECT_EQ(vpi_get(vpiDPIContext, c_f), 1);
  EXPECT_STREQ(vpi_get_str(vpiDPICIdentifier, c_f), "c_name");
  EXPECT_EQ(vpi_get(vpiDPICStr, d_t), vpiDPI);
  EXPECT_EQ(vpi_get(vpiAccessType, e_f), vpiDPIExportAcc);
  EXPECT_EQ(vpi_get(vpiDPICStr, e_f), vpiDPIC);
  EXPECT_STREQ(vpi_get_str(vpiDPICIdentifier, e_f), "e_name");
  EXPECT_NE(vpi_get(vpiAccessType, s_f), vpiDPIImportAcc);
  EXPECT_NE(vpi_get(vpiAccessType, s_f), vpiDPIExportAcc);
  EXPECT_EQ(vpi_get_str(vpiDPICIdentifier, s_f), nullptr);
}

TEST_F(TaskFuncsOfARun, AMethodHoldsItsIoDeclsAndReturnVariable) {
  Run("module top;\n"
      "  class C;\n"
      "    function logic signed [7:0] m(int a, output bit b);\n"
      "      return a; endfunction\n"
      "    task t(input int x); endtask\n"
      "  endclass\n"
      "endmodule\n");
  vpiHandle c = Named(vpiClassDefn, By("top"), "C");
  ASSERT_NE(c, nullptr);
  vpiHandle m = Named(vpiMethods, c, "m");
  ASSERT_NE(m, nullptr);
  EXPECT_EQ(NamesOf(vpiIODecl, m), (std::vector<std::string>{"a", "b"}));
  EXPECT_EQ(vpi_get(vpiDirection, Named(vpiIODecl, m, "b")), vpiOutput);
  vpiHandle ret = vpi_handle(vpiReturn, m);
  ASSERT_NE(ret, nullptr);
  EXPECT_EQ(vpi_get(vpiType, ret), vpiLogicVar);
  EXPECT_STREQ(vpi_get_str(vpiName, ret), "m");
  EXPECT_EQ(vpi_get(vpiSize, m), 8);
  EXPECT_EQ(vpi_get(vpiSigned, m), 1);
  EXPECT_EQ(vpi_get(vpiFuncType, m), vpiSizedSignedFunc);
  EXPECT_EQ(BoundOf(vpiLeftRange, m), 7);
  vpiHandle t = Named(vpiMethods, c, "t");
  ASSERT_NE(t, nullptr);
  EXPECT_EQ(NamesOf(vpiIODecl, t), (std::vector<std::string>{"x"}));
  EXPECT_EQ(vpi_handle(vpiReturn, t), nullptr);
}

TEST_F(TaskFuncsOfARun, AMethodNamesItsPackagesTypesAndItsBodysVariables) {
  Run("package pk; typedef int t;\n"
      "  class D; extern function t e(t k); endclass\n"
      "  function t D::e(t k); int loc; return k; endfunction\n"
      "endpackage\n"
      "module top; endmodule\n");
  vpiHandle e = Named(vpiMethods, Named(vpiClassDefn, By("pk"), "D"), "e");
  ASSERT_NE(e, nullptr);
  EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiReturn, e)), vpiIntVar);
  EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiExpr, Named(vpiIODecl, e, "k"))),
            vpiIntVar);
  EXPECT_EQ(VariableKindOf(e, "loc"), vpiIntVar);
}

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

TEST(TaskFuncModel, NoObjectHasNoStatement) {
  EXPECT_EQ(VpiTaskFuncStmt(nullptr), nullptr);
}

}  // namespace
}  // namespace delta
