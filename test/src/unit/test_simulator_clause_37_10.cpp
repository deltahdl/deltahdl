#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.10 instance: the VPI instance object model. These tests observe the
// production helpers in vpi.cpp and the VpiContext methods that apply the
// numbered "Details" rules of the clause. Lifetime/allocation properties
// (detail 9) belong to §37.3.7 and the `line effect on definition location
// (detail 8) belongs to §22.12, so they are exercised by those subclauses.

// D1: the vpiTypedef iteration returns only the user-defined typespecs whose
// typedefs are explicitly declared in the instance, preserving order.
TEST(InstanceModel, TypedefIterationReturnsDeclaredUserTypedefs) {
  std::vector<VpiTypeDeclEntry> entries = {
      {"my_word_t", /*user_defined=*/true, /*declared_in_instance=*/true},
      {"int", /*user_defined=*/false, /*declared_in_instance=*/true},
      {"imported_t", /*user_defined=*/true, /*declared_in_instance=*/false},
      {"my_flag_t", /*user_defined=*/true, /*declared_in_instance=*/true},
  };

  std::vector<const VpiTypeDeclEntry*> visible = VpiInstanceTypedefs(entries);
  ASSERT_EQ(visible.size(), 2u);
  EXPECT_EQ(visible[0]->name, "my_word_t");
  EXPECT_EQ(visible[1]->name, "my_flag_t");
}

// D10: the vpiNetTypedef iteration applies the same gating to user-defined
// nettypes explicitly declared in the instance.
TEST(InstanceModel, NetTypedefIterationReturnsDeclaredUserNettypes) {
  std::vector<VpiTypeDeclEntry> entries = {
      {"wire", /*user_defined=*/false, /*declared_in_instance=*/true},
      {"my_net_t", /*user_defined=*/true, /*declared_in_instance=*/true},
      {"elsewhere_net_t", /*user_defined=*/true,
       /*declared_in_instance=*/false},
  };

  std::vector<const VpiTypeDeclEntry*> visible =
      VpiInstanceNetTypedefs(entries);
  ASSERT_EQ(visible.size(), 1u);
  EXPECT_EQ(visible[0]->name, "my_net_t");
}

// D3: the four scope kinds count as instances; nothing else does.
TEST(InstanceModel, InstanceTypesAreTheFourScopeKinds) {
  EXPECT_TRUE(VpiIsInstanceType(vpiModule));
  EXPECT_TRUE(VpiIsInstanceType(vpiPackage));
  EXPECT_TRUE(VpiIsInstanceType(vpiInterface));
  EXPECT_TRUE(VpiIsInstanceType(vpiProgram));

  EXPECT_FALSE(VpiIsInstanceType(vpiNet));
  EXPECT_FALSE(VpiIsInstanceType(vpiReg));
  EXPECT_FALSE(VpiIsInstanceType(vpiPort));
}

// D3: vpiInstance returns the immediate enclosing instance, skipping
// non-instance scopes such as a named begin block.
TEST(InstanceModel, InstanceOfReturnsImmediateEnclosingInstance) {
  VpiObject program;
  program.type = vpiProgram;
  VpiObject module;
  module.type = vpiModule;
  module.parent = &program;
  VpiObject block;  // a non-instance scope inside the module
  block.type = vpiNamedBegin;
  block.parent = &module;
  VpiObject net;
  net.type = vpiNet;
  net.parent = &block;

  EXPECT_EQ(VpiInstanceOf(&net), &module);
  // An object with no enclosing instance reports none.
  VpiObject orphan;
  EXPECT_EQ(VpiInstanceOf(&orphan), nullptr);
}

// D2: vpiModule returns the nearest enclosing module, and null when the object
// lives inside a non-module instance only.
TEST(InstanceModel, ModuleOfReturnsEnclosingModuleOrNull) {
  VpiObject module;
  module.type = vpiModule;
  VpiObject net_in_module;
  net_in_module.type = vpiNet;
  net_in_module.parent = &module;
  EXPECT_EQ(VpiModuleOf(&net_in_module), &module);

  VpiObject package;
  package.type = vpiPackage;
  VpiObject var_in_package;
  var_in_package.type = vpiReg;
  var_in_package.parent = &package;
  EXPECT_EQ(VpiModuleOf(&var_in_package), nullptr);
}

// D4: the vpiMemory iteration yields array variable objects, not vpiMemory.
TEST(InstanceModel, MemoryIterationYieldsArrayVariableType) {
  EXPECT_EQ(VpiMemoryIterationItemType(), vpiRegArray);
  EXPECT_NE(VpiMemoryIterationItemType(), vpiMemory);
}

// D5: a compilation-unit object's full name is prefixed with "$unit::".
TEST(InstanceModel, CompilationUnitFullNameHasUnitPrefix) {
  EXPECT_EQ(VpiCompilationUnitFullName("top.sig"), "$unit::top.sig");
}

// D5: a package's full name is its own name ending in "::", distinguishing it
// from a module of the same name.
TEST(InstanceModel, PackageFullNameEndsWithDoubleColon) {
  EXPECT_EQ(VpiPackageFullName("my_pkg"), "my_pkg::");
  EXPECT_NE(VpiPackageFullName("my_pkg"), "my_pkg");
}

// D5: a package member's full name joins package and member with "::".
TEST(InstanceModel, PackageMemberFullNameUsesDoubleColonSeparator) {
  EXPECT_EQ(VpiPackageMemberFullName("my_pkg", "CONST"), "my_pkg::CONST");
}

// D5: "::" follows a package or class-definition scope; "." everywhere else.
TEST(InstanceModel, NameSeparatorChoosesColonsOnlyForPackageOrClassDefn) {
  EXPECT_EQ(VpiNameSeparator(/*package_or_class_defn_boundary=*/true), "::");
  EXPECT_EQ(VpiNameSeparator(/*package_or_class_defn_boundary=*/false), ".");
}

// D6: vpi_handle_by_name() refuses imported items and compilation-unit objects
// but still resolves an ordinary registered object.
TEST(InstanceModel, HandleByNameRejectsImportedAndCompilationUnitObjects) {
  VpiObject ordinary;
  VpiObject imported;
  imported.imported = true;
  VpiObject in_unit;
  in_unit.in_compilation_unit = true;

  EXPECT_TRUE(VpiHandleByNameAccessible(ordinary));
  EXPECT_FALSE(VpiHandleByNameAccessible(imported));
  EXPECT_FALSE(VpiHandleByNameAccessible(in_unit));
}

// D6 (end to end): the rejected objects are unreachable through the production
// vpi_handle_by_name() entry point, while a plain object resolves.
TEST(InstanceModel, HandleByNameEntryPointEnforcesAccessibility) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiHandle ok = ctx.CreateModule("plain", "plain");
  VpiHandle imported = ctx.CreateModule("imported", "imported");
  imported->imported = true;
  VpiHandle in_unit = ctx.CreateModule("unit_obj", "$unit::unit_obj");
  in_unit->in_compilation_unit = true;

  EXPECT_EQ(vpi_handle_by_name("plain", nullptr), ok);
  EXPECT_EQ(vpi_handle_by_name("imported", nullptr), nullptr);
  EXPECT_EQ(vpi_handle_by_name("unit_obj", nullptr), nullptr);
}

// D7: the pure smallest-precision helper takes the minimum, with an empty
// design reporting zero.
TEST(InstanceModel, SmallestTimePrecisionIsTheMinimum) {
  EXPECT_EQ(VpiSmallestTimePrecision({-9, -12, -6}), -12);
  EXPECT_EQ(VpiSmallestTimePrecision({}), 0);
}

// D7 (end to end): a null handle with vpiTimePrecision or vpiTimeUnit returns
// the smallest time precision across every module in the design.
TEST(InstanceModel, NullHandleTimePropertiesReturnSmallestModulePrecision) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiHandle coarse = ctx.CreateModule("coarse", "coarse");
  coarse->time_precision = -9;
  VpiHandle fine = ctx.CreateModule("fine", "fine");
  fine->time_precision = -12;

  EXPECT_EQ(vpi_get(vpiTimePrecision, nullptr), -12);
  EXPECT_EQ(vpi_get(vpiTimeUnit, nullptr), -12);
}

// ---------------------------------------------------------------------------
// Edge cases and error conditions for the §37.10 rules.
// ---------------------------------------------------------------------------

// D1 edge: with no typedef entries the vpiTypedef iteration yields nothing.
TEST(InstanceModel, TypedefIterationOfEmptyInstanceIsEmpty) {
  EXPECT_TRUE(VpiInstanceTypedefs({}).empty());
}

// D1 edge: an entry that is neither user-defined nor declared in the instance
// is excluded; only the gating combination survives.
TEST(InstanceModel, TypedefIterationDropsBuiltinAndUndeclaredEntries) {
  std::vector<VpiTypeDeclEntry> entries = {
      {"builtin_undeclared", /*user_defined=*/false,
       /*declared_in_instance=*/false},
      {"builtin_declared", /*user_defined=*/false,
       /*declared_in_instance=*/true},
      {"user_undeclared", /*user_defined=*/true,
       /*declared_in_instance=*/false},
  };
  EXPECT_TRUE(VpiInstanceTypedefs(entries).empty());
}

// D10 edge: with no nettype entries the vpiNetTypedef iteration yields nothing.
TEST(InstanceModel, NetTypedefIterationOfEmptyInstanceIsEmpty) {
  EXPECT_TRUE(VpiInstanceNetTypedefs({}).empty());
}

// D2 error: a null object handle has no enclosing module.
TEST(InstanceModel, ModuleOfNullHandleIsNull) {
  EXPECT_EQ(VpiModuleOf(nullptr), nullptr);
}

// D2 edge: the search skips intervening non-module scopes and still reports the
// enclosing module.
TEST(InstanceModel, ModuleOfSkipsNonModuleScopes) {
  VpiObject module;
  module.type = vpiModule;
  VpiObject block;
  block.type = vpiNamedBegin;
  block.parent = &module;
  VpiObject net;
  net.type = vpiNet;
  net.parent = &block;

  EXPECT_EQ(VpiModuleOf(&net), &module);
}

// D3 error: a null object handle has no enclosing instance.
TEST(InstanceModel, InstanceOfNullHandleIsNull) {
  EXPECT_EQ(VpiInstanceOf(nullptr), nullptr);
}

// D3 edge: the immediate instance need not be a module; an object directly in
// an interface reports that interface.
TEST(InstanceModel, InstanceOfReportsNonModuleInstance) {
  VpiObject iface;
  iface.type = vpiInterface;
  VpiObject net;
  net.type = vpiNet;
  net.parent = &iface;

  EXPECT_EQ(VpiInstanceOf(&net), &iface);
}

// D5 edge: an empty member path still produces a well-formed package boundary,
// and a compilation-unit object with an empty path is just the scope prefix.
TEST(InstanceModel, FullNameBoundariesHoldForEmptyComponents) {
  EXPECT_EQ(VpiPackageMemberFullName("pkg", ""), "pkg::");
  EXPECT_EQ(VpiCompilationUnitFullName(""), "$unit::");
}

// D6 edge: an object flagged both imported and within a compilation unit stays
// inaccessible.
TEST(InstanceModel, HandleByNameRejectsObjectThatIsImportedAndInUnit) {
  VpiObject both;
  both.imported = true;
  both.in_compilation_unit = true;
  EXPECT_FALSE(VpiHandleByNameAccessible(both));
}

// D6 error: a null name and an unregistered name both resolve to no handle.
TEST(InstanceModel, HandleByNameRejectsNullAndUnknownNames) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  EXPECT_EQ(vpi_handle_by_name(nullptr, nullptr), nullptr);
  EXPECT_EQ(vpi_handle_by_name("never_registered", nullptr), nullptr);
}

// D7 edge: a design with no modules reports a zero smallest precision, and a
// single module reports its own precision.
TEST(InstanceModel, NullHandleTimePrecisionHandlesEmptyAndSingleModule) {
  VpiContext empty_ctx;
  SetGlobalVpiContext(&empty_ctx);
  EXPECT_EQ(vpi_get(vpiTimePrecision, nullptr), 0);

  VpiContext one_ctx;
  SetGlobalVpiContext(&one_ctx);
  VpiHandle only = one_ctx.CreateModule("only", "only");
  only->time_precision = -9;
  EXPECT_EQ(vpi_get(vpiTimePrecision, nullptr), -9);
}

// D7 edge: a null handle paired with a non-time property is not a precision
// query and reports zero.
TEST(InstanceModel, NullHandleNonTimePropertyReturnsZero) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);
  EXPECT_EQ(vpi_get(vpiType, nullptr), 0);
}

}  // namespace
}  // namespace delta
