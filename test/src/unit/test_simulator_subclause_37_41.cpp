#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.41 Task and function declaration: the object model diagram draws a "task
// func" object with "function" and "task" specializations. A function reaches
// its return-capture variable through vpiReturn and carries vpiSigned/vpiSize/
// vpiFuncType; the shared "task func" carries vpiMethod, vpiAccessType,
// vpiVisibility, vpiVirtual, vpiAutomatic, and the DPI properties vpiDPIPure,
// vpiDPIContext, vpiDPICStr, and vpiDPICIdentifier. The structural edges
// (vpiLeftRange/vpiRightRange, io decl, func/task call, class defn, vpiParent)
// and the bare figure properties are descriptive or generic; the lifetime
// property vpiAutomatic belongs to §37.3.7 and vpiVirtual is reported
// generically. These tests pin the twelve numbered Details that constrain the
// model:
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

  vpiHandle reached = vpi_handle(vpiReturn, &fn);
  ASSERT_EQ(reached, &ret);
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
  EXPECT_EQ(vpi_handle(vpiReturn, &task), nullptr);
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
  EXPECT_EQ(std::string(vpi_get_str(vpiFullName, &pkg_fn)), "pkg::crc");

  VpiObject class_fn;
  class_fn.type = vpiFunction;
  class_fn.name = "run";
  class_fn.full_name =
      VpiClassMemberFullName(/*is_static=*/true, "top", "Driver", "run");
  EXPECT_EQ(std::string(vpi_get_str(vpiFullName, &class_fn)),
            "top.Driver::run");
}

// Detail 6: a DPI task or function reports vpiDPIExportAcc when it is an export
// and vpiDPIImportAcc when it is an import; a non-DPI tf is outside this rule.
TEST_F(TaskFuncDeclaration, DpiAccessTypeReportsImportAndExport) {
  VpiObject import_fn;
  import_fn.type = vpiFunction;
  import_fn.is_dpi = true;
  import_fn.dpi_export = false;
  EXPECT_EQ(vpi_get(vpiAccessType, &import_fn), vpiDPIImportAcc);

  VpiObject export_task;
  export_task.type = vpiTask;
  export_task.is_dpi = true;
  export_task.dpi_export = true;
  EXPECT_EQ(vpi_get(vpiAccessType, &export_task), vpiDPIExportAcc);

  // A plain function is not a DPI tf, so it falls through to its stored value.
  VpiObject plain_fn;
  plain_fn.type = vpiFunction;
  EXPECT_EQ(vpi_get(vpiAccessType, &plain_fn), 0);
}

// Detail 7: vpiDPIPure reports TRUE for a pure DPI import function and FALSE
// otherwise.
TEST_F(TaskFuncDeclaration, DpiPureReportedForPureImportFunction) {
  VpiObject pure_fn;
  pure_fn.type = vpiFunction;
  pure_fn.is_dpi = true;
  pure_fn.dpi_pure = true;
  EXPECT_EQ(vpi_get(vpiDPIPure, &pure_fn), 1);

  VpiObject impure_fn;
  impure_fn.type = vpiFunction;
  impure_fn.is_dpi = true;
  EXPECT_EQ(vpi_get(vpiDPIPure, &impure_fn), 0);
}

// Detail 8: vpiDPIContext reports TRUE for a context import DPI task or
// function and FALSE otherwise.
TEST_F(TaskFuncDeclaration, DpiContextReportedForContextImport) {
  VpiObject ctx_fn;
  ctx_fn.type = vpiFunction;
  ctx_fn.is_dpi = true;
  ctx_fn.dpi_context = true;
  EXPECT_EQ(vpi_get(vpiDPIContext, &ctx_fn), 1);

  VpiObject plain_fn;
  plain_fn.type = vpiFunction;
  plain_fn.is_dpi = true;
  EXPECT_EQ(vpi_get(vpiDPIContext, &plain_fn), 0);
}

// Detail 9: vpiDPICStr reports vpiDPIC for a "DPI-C" tf and vpiDPI for a "DPI"
// tf; a tf that is not a DPI tf carries no flavor.
TEST_F(TaskFuncDeclaration, DpiCStrDistinguishesDpiAndDpiC) {
  VpiObject dpi_c;
  dpi_c.type = vpiFunction;
  dpi_c.is_dpi = true;
  dpi_c.is_dpi_c = true;
  EXPECT_EQ(vpi_get(vpiDPICStr, &dpi_c), vpiDPIC);

  VpiObject dpi;
  dpi.type = vpiFunction;
  dpi.is_dpi = true;
  dpi.is_dpi_c = false;
  EXPECT_EQ(vpi_get(vpiDPICStr, &dpi), vpiDPI);

  VpiObject not_dpi;
  not_dpi.type = vpiFunction;
  EXPECT_EQ(vpi_get(vpiDPICStr, &not_dpi), 0);
}

// Detail 10: vpiDPICIdentifier reports the C linkage name of a DPI tf, and null
// when the object carries none.
TEST_F(TaskFuncDeclaration, DpiCIdentifierReportsCLinkageName) {
  VpiObject fn;
  fn.type = vpiFunction;
  fn.is_dpi = true;
  fn.dpi_c_identifier = "c_crc32";
  EXPECT_EQ(std::string(vpi_get_str(vpiDPICIdentifier, &fn)), "c_crc32");

  VpiObject no_id;
  no_id.type = vpiFunction;
  EXPECT_EQ(vpi_get_str(vpiDPICIdentifier, &no_id), nullptr);
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

}  // namespace
}  // namespace delta
