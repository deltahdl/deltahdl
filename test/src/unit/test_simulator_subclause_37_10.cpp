#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/rtlir.h"
#include "elaborator/separate_compilation_bind.h"
#include "fixture_scratch_dir.h"
#include "fixture_simulator.h"
#include "fixture_vpi_run.h"
#include "helpers_bound_from_library.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

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

// D3 (end to end): the vpiInstance relation is reachable through the production
// vpi_handle() entry point, which skips intervening non-instance scopes to
// reach the immediate enclosing instance and reports none when nothing encloses
// it.
TEST(InstanceModel, HandleVpiInstanceReachesImmediateEnclosingInstance) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject program;
  program.type = vpiProgram;
  VpiObject module;
  module.type = vpiModule;
  module.parent = &program;
  VpiObject block;  // a non-instance scope between the object and its instance
  block.type = vpiNamedBegin;
  block.parent = &module;
  VpiObject net;
  net.type = vpiNet;
  net.parent = &block;

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiInstance, VpiHandleOf(&net))), &module);

  // The immediate instance need not be a module: an object directly inside an
  // interface resolves to that interface through the same entry point.
  VpiObject iface;
  iface.type = vpiInterface;
  VpiObject iface_net;
  iface_net.type = vpiNet;
  iface_net.parent = &iface;
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiInstance, VpiHandleOf(&iface_net))),
            &iface);

  // With no enclosing instance the relation resolves to no handle.
  VpiObject orphan;
  orphan.type = vpiNet;
  EXPECT_EQ(vpi_handle(vpiInstance, VpiHandleOf(&orphan)), nullptr);
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

  EXPECT_EQ(VpiObjectOf(vpi_handle_by_name(VpiText("plain"), nullptr)), ok);
  EXPECT_EQ(vpi_handle_by_name(VpiText("imported"), nullptr), nullptr);
  EXPECT_EQ(vpi_handle_by_name(VpiText("unit_obj"), nullptr), nullptr);
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

// D3 edge: the four instance kinds all count as the immediate instance. The
// module and interface forms are covered above; here an object directly inside
// a package resolves to that package, and one directly inside a program
// resolves to that program.
TEST(InstanceModel, InstanceOfResolvesPackageAndProgramInstances) {
  VpiObject package;
  package.type = vpiPackage;
  VpiObject const_in_package;
  const_in_package.type = vpiReg;
  const_in_package.parent = &package;
  EXPECT_EQ(VpiInstanceOf(&const_in_package), &package);

  VpiObject program;
  program.type = vpiProgram;
  VpiObject net_in_program;
  net_in_program.type = vpiNet;
  net_in_program.parent = &program;
  EXPECT_EQ(VpiInstanceOf(&net_in_program), &program);
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
  EXPECT_EQ(vpi_handle_by_name(VpiText("never_registered"), nullptr), nullptr);
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

// A design run with a PLI application registered, its VPI model read back
// once the run is over.
class InstanceObjectsOfARun : public VpiDesignRun {};

constexpr const char* kEmptyInstances =
    "module leafm; endmodule\n"
    "module sub; leafm leaf(); endmodule\n"
    "module top; sub m1(); sub m2(); endmodule\n";

// §37.10: every module instance is an object, whether or not it declares
// anything, so the instances of top are its vpiModule children.
TEST_F(InstanceObjectsOfARun, InstancesDeclaringNothingAreObjects) {
  Run(kEmptyInstances);
  EXPECT_EQ(NamesOf(vpiModule, vpi_handle_by_name(VpiText("top"), nullptr)),
            (std::vector<std::string>{"m1", "m2"}));
}

// And an instance below one is reached by its full name, under its parent.
TEST_F(InstanceObjectsOfARun, ADeepInstanceDeclaringNothingHasItsParent) {
  Run(kEmptyInstances);
  vpiHandle leaf = vpi_handle_by_name(VpiText("top.m2.leaf"), nullptr);
  ASSERT_NE(leaf, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, vpi_handle(vpiModule, leaf)), "top.m2");
}

constexpr const char* kDottedEscapedNames =
    "module sub; endmodule\n"
    "module top; logic \\a.b ; sub \\u.1 (); endmodule\n";

// §37.10 with §5.6.1: an escaped identifier may hold a period and is still one
// name, so the variable and the instance written with one are one object each
// under top, named with the period, and no scope is made for the text before
// it.
TEST_F(InstanceObjectsOfARun, AnEscapedNameHoldingAPeriodIsOneObject) {
  Run(kDottedEscapedNames);
  vpiHandle top = By("top");
  EXPECT_EQ(NamesOf(vpiModule, nullptr), (std::vector<std::string>{"top"}));
  EXPECT_EQ(NamesOf(vpiModule, top), (std::vector<std::string>{"u.1"}));
  EXPECT_EQ(NamesOf(vpiVariables, top), (std::vector<std::string>{"a.b"}));
  EXPECT_EQ(VpiObjectOf(By("top.\\a.b ")),
            VpiObjectOf(Named(vpiVariables, top, "a.b")));
}

// The instance is found again by that one name where its definition is
// recorded, so it reports the module it instantiates.
TEST_F(InstanceObjectsOfARun, AnInstanceNamedWithAPeriodHasItsDefinition) {
  Run(kDottedEscapedNames);
  EXPECT_STREQ(vpi_get_str(vpiDefName, By("top.\\u.1 ")), "sub");
}

// A cell bound from a precompiled library keeps such a name whole too: its
// record is parsed into a unit of its own and its declarations moved onto the
// one the design is elaborated from, with the names that hold a period.
TEST_F(InstanceObjectsOfARun, AnEscapedNameInALibraryCellIsOneObject) {
  ScratchDir tmp;
  SeparateCompilationBinder binder(f_.mgr, f_.arena, f_.diag);
  RtlirDesign* design = BoundFromALibrary(
      tmp, {"module t; logic \\a.b ; endmodule\n"}, "", binder);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f_.diag.HasErrors());
  LowerAndRun(design, f_);
  EXPECT_EQ(NamesOf(vpiVariables, By("t")), (std::vector<std::string>{"a.b"}));
}

// A sibling named by the text before the period does not take the instance's
// place: u.1 is found again as itself, not as a child 1 of u that does not
// exist, so both instances report their definition.
TEST_F(InstanceObjectsOfARun, AnInstanceNamedWithAPeriodBesideItsPrefix) {
  Run("module sub; endmodule\n"
      "module top; sub u (); sub \\u.1 (); endmodule\n");
  EXPECT_EQ(NamesOf(vpiModule, By("top")),
            (std::vector<std::string>{"u", "u.1"}));
  EXPECT_STREQ(vpi_get_str(vpiDefName, By("top.u")), "sub");
  EXPECT_STREQ(vpi_get_str(vpiDefName, By("top.\\u.1 ")), "sub");
}

constexpr const char* kPackageBesideTop =
    "package pkg; int pv = 8; endpackage\n"
    "module top; int x = pkg::pv; endmodule\n";

// §37.10: a package is an instance of its own, reached from no scope.
TEST_F(InstanceObjectsOfARun, APackageIsReachedFromNoScope) {
  Run(kPackageBesideTop);
  EXPECT_EQ(NamesOf(vpiPackage, nullptr), (std::vector<std::string>{"pkg"}));
}

// Detail 5: its full name is its name followed by "::".
TEST_F(InstanceObjectsOfARun, APackagesFullNameEndsInColons) {
  Run(kPackageBesideTop);
  vpiHandle it = vpi_iterate(vpiPackage, nullptr);
  ASSERT_NE(it, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, vpi_scan(it)), "pkg::");
}

// Detail 5: a member's full name joins the package's to its own with "::".
TEST_F(InstanceObjectsOfARun, APackageMembersFullNameUsesColons) {
  Run(kPackageBesideTop);
  vpiHandle it = vpi_iterate(vpiPackage, nullptr);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(FullNameOfChild(vpi_scan(it), "pv"), "pkg::pv");
}

// The package is no part of the top that happens to be beside it.
TEST_F(InstanceObjectsOfARun, APackageIsNoChildOfTheTop) {
  Run(kPackageBesideTop);
  EXPECT_EQ(FullNameOfChild(vpi_handle_by_name(VpiText("top"), nullptr), "pkg"),
            "");
}

// Detail 6: an imported item is not reached by name through the scope that
// imported it.
TEST_F(InstanceObjectsOfARun, AnImportedItemIsNotReachedThroughTheImporter) {
  Run("package pkg; parameter int P = 42; endpackage\n"
      "module top; import pkg::P; int x = P; endmodule\n");
  EXPECT_EQ(vpi_handle_by_name(VpiText("top.P"), nullptr), nullptr);
}

constexpr const char* kUnitItemBesideTop =
    "int g = 3;\n"
    "module top; int x = $unit::g; endmodule\n";

// Detail 6: an object of the compilation unit is not reached by name.
TEST_F(InstanceObjectsOfARun, ACompilationUnitItemIsNotReachedByName) {
  Run(kUnitItemBesideTop);
  EXPECT_EQ(vpi_handle_by_name(VpiText("$unit.g"), nullptr), nullptr);
}

// The compilation unit is no part of the top beside it.
TEST_F(InstanceObjectsOfARun, ACompilationUnitIsNoChildOfTheTop) {
  Run(kUnitItemBesideTop);
  EXPECT_EQ(
      FullNameOfChild(vpi_handle_by_name(VpiText("top"), nullptr), "$unit"),
      "");
}

// Detail 5: the full name of an object of the compilation unit begins with
// "$unit::". The unit is drawn as a package, reached from no scope.
TEST_F(InstanceObjectsOfARun, ACompilationUnitItemsFullNameUsesColons) {
  Run(kUnitItemBesideTop);
  vpiHandle it = vpi_iterate(vpiPackage, nullptr);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(FullNameOfChild(vpi_scan(it), "g"), "$unit::g");
}

constexpr const char* kTwoTimescales =
    "module sub; timeunit 1us; timeprecision 1ps; endmodule\n"
    "module top; timeunit 10ns; timeprecision 1ns; sub s(); endmodule\n";

// §37.10: an instance has the time unit of its definition, as a power of ten
// of a second: 10 ns is -8.
TEST_F(InstanceObjectsOfARun, AnInstanceHasItsTimeUnit) {
  Run(kTwoTimescales);
  EXPECT_EQ(vpi_get(vpiTimeUnit, vpi_handle_by_name(VpiText("top"), nullptr)),
            -8);
}

TEST_F(InstanceObjectsOfARun, AnInstanceHasItsTimePrecision) {
  Run(kTwoTimescales);
  EXPECT_EQ(
      vpi_get(vpiTimePrecision, vpi_handle_by_name(VpiText("top.s"), nullptr)),
      -12);
}

// Detail 7: NULL asks for the smallest precision of all the design's modules.
TEST_F(InstanceObjectsOfARun, NoObjectHasTheSmallestPrecision) {
  Run(kTwoTimescales);
  EXPECT_EQ(vpi_get(vpiTimePrecision, nullptr), -12);
}

// §37.10: an instance has the line and file of its definition: sub is
// defined on line 1 and instantiated on line 2.
TEST_F(InstanceObjectsOfARun, AnInstanceHasItsDefinitionsLine) {
  Run(kTwoTimescales);
  EXPECT_EQ(
      vpi_get(vpiDefLineNo, vpi_handle_by_name(VpiText("top.s"), nullptr)), 1);
}

TEST_F(InstanceObjectsOfARun, AnInstanceHasItsDefinitionsFile) {
  Run(kTwoTimescales);
  EXPECT_STREQ(
      vpi_get_str(vpiDefFile, vpi_handle_by_name(VpiText("top.s"), nullptr)),
      "<test>");
}

// Detail 1: a package is an instance, whose vpiTypedef iteration returns the
// typespecs of the typedefs it declares, each named in the package with "::"
// (detail 5) and of the kind its type is (§37.25) (#5742).
TEST_F(InstanceObjectsOfARun, APackageReachesTheTypedefsItDeclares) {
  Run("package pk; typedef logic [3:0] nib_t; typedef int word_t;\n"
      "endpackage\n"
      "module top; endmodule\n");
  vpiHandle pk = By("pk");
  ASSERT_NE(pk, nullptr);
  EXPECT_EQ(NamesOf(vpiTypedef, pk),
            (std::vector<std::string>{"nib_t", "word_t"}));
  vpiHandle nib = Named(vpiTypedef, pk, "nib_t");
  ASSERT_NE(nib, nullptr);
  EXPECT_EQ(vpi_get(vpiType, nib), vpiLogicTypespec);
  EXPECT_STREQ(vpi_get_str(vpiFullName, nib), "pk::nib_t");
  EXPECT_EQ(vpi_get(vpiType, Named(vpiTypedef, pk, "word_t")), vpiIntTypespec);
}

// §37.10: vpiTimeUnit and vpiTimePrecision are drawn on an instance, and a
// net reports vpiUndefined for both.
TEST(InstanceModel, ANonInstanceHasNoTimeUnitOrPrecision) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);
  VpiObject net;
  net.type = vpiNet;
  EXPECT_EQ(vpi_get(vpiTimeUnit, VpiHandleOf(&net)), vpiUndefined);
  EXPECT_EQ(vpi_get(vpiTimePrecision, VpiHandleOf(&net)), vpiUndefined);
  SetGlobalVpiContext(nullptr);
}

}  // namespace
}  // namespace delta
