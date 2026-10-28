#include <gtest/gtest.h>

#include <algorithm>
#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "elaborator/separate_compilation_bind.h"
#include "fixture_scratch_dir.h"
#include "fixture_simulator.h"
#include "fixture_vpi_run.h"
#include "helpers_bound_from_library.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_design_attach_build.h"
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

// D5: a name a scope declares is joined to an instance's full name with a dot
// and to a package's or a compilation unit's, which end in "::", directly; one
// no scope object holds is the compilation unit's, under "$unit::".
TEST(InstanceModel, AScopedFullNameJoinsTheScopesOwn) {
  VpiObject top;
  top.full_name = "top";
  VpiObject pkg;
  pkg.full_name = "pkg::";
  EXPECT_EQ(VpiScopedFullName(&top, "x"), "top.x");
  EXPECT_EQ(VpiScopedFullName(&pkg, "x"), "pkg::x");
  EXPECT_EQ(VpiScopedFullName(nullptr, "x"), "$unit::x");
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
// query; it names no object, an error answered with vpiUndefined (§38.6).
TEST(InstanceModel, NullHandleNonTimePropertyIsUndefined) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);
  EXPECT_EQ(vpi_get(vpiType, nullptr), vpiUndefined);
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

// Detail 2: vpiModule is the module an object is inside, reached through a
// generate scope or an interface instance standing between, the module an
// instance is instantiated in for a module instance, and null for a top module,
// which no module encloses.
TEST_F(InstanceObjectsOfARun, VpiModuleIsTheModuleAnObjectIsInside) {
  Run("module m; endmodule\n"
      "interface ifc; wire w; endinterface\n"
      "module top; m m1(); ifc i();\n"
      "  if (1) begin : g wire gw; end endmodule\n");
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiModule, By("top.m1"))), VpiObjectOf(top));
  ASSERT_NE(By("top.g.gw"), nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiModule, By("top.g.gw"))),
            VpiObjectOf(top));
  ASSERT_NE(By("top.i.w"), nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiModule, By("top.i.w"))),
            VpiObjectOf(top));
  EXPECT_EQ(vpi_handle(vpiModule, top), nullptr);
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

// The spec param arrow: a specparam the module body declares and one a
// specify block declares are spec param objects of the instance, reached
// through vpiSpecParam and named and full-named in it, and are not among its
// variables; a PATHPULSE$ specparam, which sets the paths' pulse limits
// (§30.7.1), stands as none (#6985).
TEST_F(InstanceObjectsOfARun, AnInstancesSpecparamsAreSpecParams) {
  Run("module top(input a, output b);\n"
      "  specparam d = 1;\n"
      "  logic v;\n"
      "  specify\n"
      "    specparam tpd = 2;\n"
      "    specparam PATHPULSE$ = (1, 2);\n"
      "    (a => b) = tpd;\n"
      "  endspecify\n"
      "  assign b = a;\n"
      "endmodule\n");
  vpiHandle top = By("top");
  std::vector<std::string> names = NamesOf(vpiSpecParam, top);
  std::ranges::sort(names);
  EXPECT_EQ(names, (std::vector<std::string>{"d", "tpd"}));
  vpiHandle d = Named(vpiSpecParam, top, "d");
  ASSERT_NE(d, nullptr);
  EXPECT_EQ(vpi_get(vpiType, d), vpiSpecParam);
  EXPECT_STREQ(vpi_get_str(vpiFullName, Named(vpiSpecParam, top, "tpd")),
               "top.tpd");
  EXPECT_EQ(NamesOf(vpiVariables, top), (std::vector<std::string>{"v"}));
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

// §37.10: a package is an instance of its own, reached from no scope, as the
// compilation unit beside it is (§3.12.1), its scope declaring nothing.
TEST_F(InstanceObjectsOfARun, APackageIsReachedFromNoScope) {
  Run(kPackageBesideTop);
  EXPECT_EQ(NamesOf(vpiPackage, nullptr),
            (std::vector<std::string>{"$unit", "pkg"}));
}

// Detail 5: its full name is its name followed by "::".
TEST_F(InstanceObjectsOfARun, APackagesFullNameEndsInColons) {
  Run(kPackageBesideTop);
  vpiHandle pkg = Named(vpiPackage, nullptr, "pkg");
  ASSERT_NE(pkg, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, pkg), "pkg::");
}

// Detail 5: a member's full name joins the package's to its own with "::".
TEST_F(InstanceObjectsOfARun, APackageMembersFullNameUsesColons) {
  Run(kPackageBesideTop);
  vpiHandle pkg = Named(vpiPackage, nullptr, "pkg");
  ASSERT_NE(pkg, nullptr);
  EXPECT_EQ(FullNameOfChild(pkg, "pv"), "pkg::pv");
}

// §3.12.1 (printed page 56): the PLI traverses every compilation unit, and a
// design has one whether or not its scope declares anything. A design of one
// module reaches its unit as the one package, vpiUnit TRUE, named "$unit" and
// full-named "$unit::".
TEST_F(InstanceObjectsOfARun, ACompilationUnitDeclaringNothingIsReached) {
  Run("module top; endmodule\n");
  std::vector<vpiHandle> reached = ObjectsOf(vpiPackage, nullptr);
  ASSERT_EQ(reached.size(), 1u);
  EXPECT_EQ(vpi_get(vpiUnit, reached[0]), 1);
  EXPECT_STREQ(vpi_get_str(vpiName, reached[0]), "$unit");
  EXPECT_STREQ(vpi_get_str(vpiFullName, reached[0]), "$unit::");
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

// The figure: an instance reports the compiler directives in force where its
// definition was written -- vpiDefDelayMode the mode Annex E.4 to E.7 selected,
// vpiUnconnDrive the pull of `unconnected_drive (§22.9), vpiDefNetType the
// net type of `default_nettype (§22.8), vpiCellInstance whether `celldefine
// covered it (§22.10) -- and vpiTop whether it is a top. The run is elaborated
// without the preprocessor, so each module is given what the directives ahead
// of it record.
TEST_F(InstanceObjectsOfARun, AnInstanceReportsItsDefinitionsDirectives) {
  RtlirDesign* design = ElaborateSrc(
      "module m0; endmodule\n"
      "module m1; endmodule\n"
      "module m2; endmodule\n"
      "module m3; endmodule\n"
      "module m4; endmodule\n"
      "module top; m0 u0(); m1 u1(); m2 u2(); m3 u3(); m4 u4(); endmodule\n",
      f_);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f_.has_errors);
  struct Directives {
    DelayModeDirective delay;
    NetType drive;
    NetType nettype;
  };
  const Directives kGiven[] = {
      {DelayModeDirective::kDistributed, NetType::kTri1, NetType::kNone},
      {DelayModeDirective::kPath, NetType::kTri0, NetType::kWand},
      {DelayModeDirective::kUnit, NetType::kWire, NetType::kWire},
      {DelayModeDirective::kZero, NetType::kWire, NetType::kWire},
      {DelayModeDirective::kNone, NetType::kWire, NetType::kWire}};
  RtlirModule* top = design->top_modules.front();
  ASSERT_EQ(top->children.size(), 5u);
  for (size_t k = 0; k < 5; ++k) {
    RtlirModule* mod = top->children[k].resolved;
    mod->delay_mode = kGiven[k].delay;
    mod->unconnected_drive = kGiven[k].drive;
    mod->default_nettype = kGiven[k].nettype;
  }
  for (ModuleDecl* decl : design->compilation_unit->modules) {
    if (decl->name == "m0") decl->is_cell = true;
  }
  LowerAndRun(design, f_);
  const int kModes[] = {vpiDelayModeDistrib, vpiDelayModePath, vpiDelayModeUnit,
                        vpiDelayModeZero, vpiDelayModeNone};
  for (size_t k = 0; k < 5; ++k) {
    EXPECT_EQ(vpi_get(vpiDefDelayMode, By("top.u" + std::to_string(k))),
              kModes[k]);
  }
  EXPECT_EQ(vpi_get(vpiUnconnDrive, By("top.u0")), vpiPull1);
  EXPECT_EQ(vpi_get(vpiUnconnDrive, By("top.u1")), vpiPull0);
  EXPECT_EQ(vpi_get(vpiUnconnDrive, By("top.u4")), vpiHighZ);
  EXPECT_EQ(vpi_get(vpiDefNetType, By("top.u0")), vpiNone);
  EXPECT_EQ(vpi_get(vpiDefNetType, By("top.u1")), vpiWand);
  EXPECT_EQ(vpi_get(vpiDefNetType, By("top.u4")), vpiWire);
  EXPECT_EQ(vpi_get(vpiCellInstance, By("top.u0")), 1);
  EXPECT_EQ(vpi_get(vpiCellInstance, By("top.u4")), 0);
  EXPECT_EQ(vpi_get(vpiTop, By("top")), 1);
  EXPECT_EQ(vpi_get(vpiTop, By("top.u0")), 0);
  // §34: no envelope contained these definitions.
  EXPECT_EQ(vpi_get(vpiProtected, By("top.u0")), 0);
}

// The figure: an instance whose definition a decryption envelope contained
// reports vpiProtected TRUE, whatever its own instantiation is.
TEST(InstanceModel, AnInstanceOfAProtectedDefinitionIsProtected) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);
  VpiObject mod;
  mod.type = kVpiModule;
  mod.instance_facts.protected_definition = true;
  EXPECT_EQ(vpi_get(vpiProtected, VpiHandleOf(&mod)), 1);
  SetGlobalVpiContext(nullptr);
}

// The figure: vpiUnit is TRUE for the package that is the compilation unit's
// scope and FALSE for a declared package; a module has no such property.
TEST_F(InstanceObjectsOfARun, TheCompilationUnitIsTheUnitPackage) {
  Run("int g = 3;\n"
      "package pk; int p; endpackage\n"
      "module top; int x = $unit::g; endmodule\n");
  std::vector<std::string> units;
  vpiHandle it = vpi_iterate(vpiPackage, nullptr);
  ASSERT_NE(it, nullptr);
  while (vpiHandle pkg = vpi_scan(it)) {
    if (vpi_get(vpiUnit, pkg) == 1)
      units.emplace_back(vpi_get_str(vpiName, pkg));
  }
  EXPECT_EQ(units, std::vector<std::string>{"$unit"});
  EXPECT_EQ(vpi_get(vpiUnit, By("pk")), 0);
  EXPECT_EQ(vpi_get(vpiUnit, By("top")), 0);
}

// The figure: every instance names its definition, library, cell and
// configuration, an interface's, a program's and a package's as a module's,
// and a top is an instance of its own definition (§33.7, §38.11).
TEST_F(InstanceObjectsOfARun, EveryInstanceNamesItsDefinitionAndCell) {
  Run("interface ifc; endinterface\n"
      "program prg; endprogram\n"
      "package pk; int p; endpackage\n"
      "module top; ifc i(); prg p(); endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiCell, By("top")), "top");
  EXPECT_STREQ(vpi_get_str(vpiCell, By("top.i")), "ifc");
  EXPECT_STREQ(vpi_get_str(vpiCell, By("top.p")), "prg");
  EXPECT_STREQ(vpi_get_str(vpiCell, By("pk")), "pk");
  EXPECT_STREQ(vpi_get_str(vpiDefName, By("pk")), "pk");
  // An interface and a program are bound from the library the design was
  // compiled into, as a module is; a package is bound from none.
  EXPECT_STREQ(vpi_get_str(vpiLibrary, By("top.i")), "work");
  EXPECT_STREQ(vpi_get_str(vpiLibrary, By("top.p")), "work");
  EXPECT_STREQ(vpi_get_str(vpiLibrary, By("pk")), "");
  for (const char* name : {"top.i", "top.p", "pk"}) {
    EXPECT_STREQ(vpi_get_str(vpiConfig, By(name)), "") << name;
  }
}

// Detail 10: an instance's vpiNetTypedef iteration reaches the nettypes it
// declares, a nettype no net uses among them, and none a package declares,
// which the package reaches. §37.23 detail 2: an alias reaches the nettype it
// aliases, and a nettype of a typedef's type aliases none.
TEST_F(InstanceObjectsOfARun, AnInstanceReachesTheNettypesItDeclares) {
  Run("package pk; nettype logic pnt; endpackage\n"
      "module top;\n"
      "  typedef logic [3:0] nib_t;\n"
      "  nettype logic [3:0] bnt;\n"
      "  nettype bnt alias_nt;\n"
      "  nettype nib_t nnt;\n"
      "  pk::pnt n;\n"
      "endmodule\n");
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  EXPECT_EQ(NamesOf(vpiNetTypedef, top),
            (std::vector<std::string>{"alias_nt", "bnt", "nnt"}));
  EXPECT_EQ(NamesOf(vpiNetTypedef, By("pk")), std::vector<std::string>{"pnt"});
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiNetTypedefAlias,
                                   Named(vpiNetTypedef, top, "alias_nt"))),
            VpiObjectOf(Named(vpiNetTypedef, top, "bnt")));
  EXPECT_EQ(vpi_handle(vpiNetTypedefAlias, Named(vpiNetTypedef, top, "nnt")),
            nullptr);
}

// Detail 10 with §3.12.1: a nettype the compilation unit declares is a
// nettype decl of the unit's scope, "$unit::" naming it (detail 5), which a
// unit declaring nothing else has too; the top beside it declares none.
TEST_F(InstanceObjectsOfARun, TheCompilationUnitReachesTheNettypesItDeclares) {
  Run("nettype logic [3:0] unt;\n"
      "module top; endmodule\n");
  std::vector<std::string> reached;
  vpiHandle it = vpi_iterate(vpiPackage, nullptr);
  ASSERT_NE(it, nullptr);
  while (vpiHandle pkg = vpi_scan(it)) {
    if (vpi_get(vpiUnit, pkg) != 1) continue;
    for (vpiHandle decl : ObjectsOf(vpiNetTypedef, pkg)) {
      reached.emplace_back(vpi_get_str(vpiFullName, decl));
    }
  }
  EXPECT_EQ(reached, std::vector<std::string>{"$unit::unt"});
  EXPECT_TRUE(NamesOf(vpiNetTypedef, By("top")).empty());
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
