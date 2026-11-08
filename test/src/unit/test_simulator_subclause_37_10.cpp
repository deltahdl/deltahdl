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

TEST(InstanceModel, TypedefIterationReturnsDeclaredUserTypedefs) {
  std::vector<VpiTypeDeclEntry> entries = {
      {"my_word_t", true, true},
      {"int", false, true},
      {"imported_t", true, false},
      {"my_flag_t", true, true},
  };

  std::vector<const VpiTypeDeclEntry*> visible = VpiInstanceTypedefs(entries);
  ASSERT_EQ(visible.size(), 2u);
  EXPECT_EQ(visible[0]->name, "my_word_t");
  EXPECT_EQ(visible[1]->name, "my_flag_t");
}

TEST(InstanceModel, NetTypedefIterationReturnsDeclaredUserNettypes) {
  std::vector<VpiTypeDeclEntry> entries = {
      {"wire", false, true},
      {"my_net_t", true, true},
      {"elsewhere_net_t", true, false},
  };

  std::vector<const VpiTypeDeclEntry*> visible =
      VpiInstanceNetTypedefs(entries);
  ASSERT_EQ(visible.size(), 1u);
  EXPECT_EQ(visible[0]->name, "my_net_t");
}

TEST(InstanceModel, InstanceTypesAreTheFourScopeKinds) {
  EXPECT_TRUE(VpiIsInstanceType(vpiModule));
  EXPECT_TRUE(VpiIsInstanceType(vpiPackage));
  EXPECT_TRUE(VpiIsInstanceType(vpiInterface));
  EXPECT_TRUE(VpiIsInstanceType(vpiProgram));

  EXPECT_FALSE(VpiIsInstanceType(vpiNet));
  EXPECT_FALSE(VpiIsInstanceType(vpiReg));
  EXPECT_FALSE(VpiIsInstanceType(vpiPort));
}

TEST(InstanceModel, InstanceOfReturnsImmediateEnclosingInstance) {
  VpiObject program;
  program.type = vpiProgram;
  VpiObject module;
  module.type = vpiModule;
  module.parent = &program;
  VpiObject block;
  block.type = vpiNamedBegin;
  block.parent = &module;
  VpiObject net;
  net.type = vpiNet;
  net.parent = &block;

  EXPECT_EQ(VpiInstanceOf(&net), &module);
  VpiObject orphan;
  EXPECT_EQ(VpiInstanceOf(&orphan), nullptr);
}

TEST(InstanceModel, HandleVpiInstanceReachesImmediateEnclosingInstance) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject program;
  program.type = vpiProgram;
  VpiObject module;
  module.type = vpiModule;
  module.parent = &program;
  VpiObject block;
  block.type = vpiNamedBegin;
  block.parent = &module;
  VpiObject net;
  net.type = vpiNet;
  net.parent = &block;

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiInstance, VpiHandleOf(&net))), &module);

  VpiObject iface;
  iface.type = vpiInterface;
  VpiObject iface_net;
  iface_net.type = vpiNet;
  iface_net.parent = &iface;
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiInstance, VpiHandleOf(&iface_net))),
            &iface);

  VpiObject orphan;
  orphan.type = vpiNet;
  EXPECT_EQ(vpi_handle(vpiInstance, VpiHandleOf(&orphan)), nullptr);
}

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

TEST(InstanceModel, MemoryIterationYieldsArrayVariableType) {
  EXPECT_EQ(VpiMemoryIterationItemType(), vpiRegArray);
  EXPECT_NE(VpiMemoryIterationItemType(), vpiMemory);
}

TEST(InstanceModel, CompilationUnitFullNameHasUnitPrefix) {
  EXPECT_EQ(VpiCompilationUnitFullName("top.sig"), "$unit::top.sig");
}

TEST(InstanceModel, AScopedFullNameJoinsTheScopesOwn) {
  VpiObject top;
  top.full_name = "top";
  VpiObject pkg;
  pkg.full_name = "pkg::";
  EXPECT_EQ(VpiScopedFullName(&top, "x"), "top.x");
  EXPECT_EQ(VpiScopedFullName(&pkg, "x"), "pkg::x");
  EXPECT_EQ(VpiScopedFullName(nullptr, "x"), "$unit::x");
}

TEST(InstanceModel, PackageFullNameEndsWithDoubleColon) {
  EXPECT_EQ(VpiPackageFullName("my_pkg"), "my_pkg::");
  EXPECT_NE(VpiPackageFullName("my_pkg"), "my_pkg");
}

TEST(InstanceModel, PackageMemberFullNameUsesDoubleColonSeparator) {
  EXPECT_EQ(VpiPackageMemberFullName("my_pkg", "CONST"), "my_pkg::CONST");
}

TEST(InstanceModel, NameSeparatorChoosesColonsOnlyForPackageOrClassDefn) {
  EXPECT_EQ(VpiNameSeparator(true), "::");
  EXPECT_EQ(VpiNameSeparator(false), ".");
}

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

TEST(InstanceModel, SmallestTimePrecisionIsTheMinimum) {
  EXPECT_EQ(VpiSmallestTimePrecision({-9, -12, -6}), -12);
  EXPECT_EQ(VpiSmallestTimePrecision({}), 0);
}

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

TEST(InstanceModel, TypedefIterationOfEmptyInstanceIsEmpty) {
  EXPECT_TRUE(VpiInstanceTypedefs({}).empty());
}

TEST(InstanceModel, TypedefIterationDropsBuiltinAndUndeclaredEntries) {
  std::vector<VpiTypeDeclEntry> entries = {
      {"builtin_undeclared", false, false},
      {"builtin_declared", false, true},
      {"user_undeclared", true, false},
  };
  EXPECT_TRUE(VpiInstanceTypedefs(entries).empty());
}

TEST(InstanceModel, NetTypedefIterationOfEmptyInstanceIsEmpty) {
  EXPECT_TRUE(VpiInstanceNetTypedefs({}).empty());
}

TEST(InstanceModel, ModuleOfNullHandleIsNull) {
  EXPECT_EQ(VpiModuleOf(nullptr), nullptr);
}

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

TEST(InstanceModel, InstanceOfNullHandleIsNull) {
  EXPECT_EQ(VpiInstanceOf(nullptr), nullptr);
}

TEST(InstanceModel, InstanceOfReportsNonModuleInstance) {
  VpiObject iface;
  iface.type = vpiInterface;
  VpiObject net;
  net.type = vpiNet;
  net.parent = &iface;

  EXPECT_EQ(VpiInstanceOf(&net), &iface);
}

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

TEST(InstanceModel, FullNameBoundariesHoldForEmptyComponents) {
  EXPECT_EQ(VpiPackageMemberFullName("pkg", ""), "pkg::");
  EXPECT_EQ(VpiCompilationUnitFullName(""), "$unit::");
}

TEST(InstanceModel, HandleByNameRejectsObjectThatIsImportedAndInUnit) {
  VpiObject both;
  both.imported = true;
  both.in_compilation_unit = true;
  EXPECT_FALSE(VpiHandleByNameAccessible(both));
}

TEST(InstanceModel, HandleByNameRejectsNullAndUnknownNames) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  EXPECT_EQ(vpi_handle_by_name(nullptr, nullptr), nullptr);
  EXPECT_EQ(vpi_handle_by_name(VpiText("never_registered"), nullptr), nullptr);
}

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

TEST(InstanceModel, NullHandleNonTimePropertyIsUndefined) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);
  EXPECT_EQ(vpi_get(vpiType, nullptr), vpiUndefined);
}

class InstanceObjectsOfARun : public VpiDesignRun {};

constexpr const char* kEmptyInstances =
    "module leafm; endmodule\n"
    "module sub; leafm leaf(); endmodule\n"
    "module top; sub m1(); sub m2(); endmodule\n";

TEST_F(InstanceObjectsOfARun, InstancesDeclaringNothingAreObjects) {
  Run(kEmptyInstances);
  EXPECT_EQ(NamesOf(vpiModule, vpi_handle_by_name(VpiText("top"), nullptr)),
            (std::vector<std::string>{"m1", "m2"}));
}

TEST_F(InstanceObjectsOfARun, ADeepInstanceDeclaringNothingHasItsParent) {
  Run(kEmptyInstances);
  vpiHandle leaf = vpi_handle_by_name(VpiText("top.m2.leaf"), nullptr);
  ASSERT_NE(leaf, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, vpi_handle(vpiModule, leaf)), "top.m2");
}

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

TEST_F(InstanceObjectsOfARun, AnEscapedNameHoldingAPeriodIsOneObject) {
  Run(kDottedEscapedNames);
  vpiHandle top = By("top");
  EXPECT_EQ(NamesOf(vpiModule, nullptr), (std::vector<std::string>{"top"}));
  EXPECT_EQ(NamesOf(vpiModule, top), (std::vector<std::string>{"u.1"}));
  EXPECT_EQ(NamesOf(vpiVariables, top), (std::vector<std::string>{"a.b"}));
  EXPECT_EQ(VpiObjectOf(By("top.\\a.b ")),
            VpiObjectOf(Named(vpiVariables, top, "a.b")));
}

TEST_F(InstanceObjectsOfARun, AnInstanceNamedWithAPeriodHasItsDefinition) {
  Run(kDottedEscapedNames);
  EXPECT_STREQ(vpi_get_str(vpiDefName, By("top.\\u.1 ")), "sub");
}

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

TEST_F(InstanceObjectsOfARun, APackageIsReachedFromNoScope) {
  Run(kPackageBesideTop);
  EXPECT_EQ(NamesOf(vpiPackage, nullptr),
            (std::vector<std::string>{"$unit", "pkg"}));
}

TEST_F(InstanceObjectsOfARun, APackagesFullNameEndsInColons) {
  Run(kPackageBesideTop);
  vpiHandle pkg = Named(vpiPackage, nullptr, "pkg");
  ASSERT_NE(pkg, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, pkg), "pkg::");
}

TEST_F(InstanceObjectsOfARun, APackageMembersFullNameUsesColons) {
  Run(kPackageBesideTop);
  vpiHandle pkg = Named(vpiPackage, nullptr, "pkg");
  ASSERT_NE(pkg, nullptr);
  EXPECT_EQ(FullNameOfChild(pkg, "pv"), "pkg::pv");
}

TEST_F(InstanceObjectsOfARun, ACompilationUnitDeclaringNothingIsReached) {
  Run("module top; endmodule\n");
  std::vector<vpiHandle> reached = ObjectsOf(vpiPackage, nullptr);
  ASSERT_EQ(reached.size(), 1u);
  EXPECT_EQ(vpi_get(vpiUnit, reached[0]), 1);
  EXPECT_STREQ(vpi_get_str(vpiName, reached[0]), "$unit");
  EXPECT_STREQ(vpi_get_str(vpiFullName, reached[0]), "$unit::");
}

TEST_F(InstanceObjectsOfARun, APackageIsNoChildOfTheTop) {
  Run(kPackageBesideTop);
  EXPECT_EQ(FullNameOfChild(vpi_handle_by_name(VpiText("top"), nullptr), "pkg"),
            "");
}

TEST_F(InstanceObjectsOfARun, AnImportedItemIsNotReachedThroughTheImporter) {
  Run("package pkg; parameter int P = 42; endpackage\n"
      "module top; import pkg::P; int x = P; endmodule\n");
  EXPECT_EQ(vpi_handle_by_name(VpiText("top.P"), nullptr), nullptr);
}

constexpr const char* kUnitItemBesideTop =
    "int g = 3;\n"
    "module top; int x = $unit::g; endmodule\n";

TEST_F(InstanceObjectsOfARun, ACompilationUnitItemIsNotReachedByName) {
  Run(kUnitItemBesideTop);
  EXPECT_EQ(vpi_handle_by_name(VpiText("$unit.g"), nullptr), nullptr);
}

TEST_F(InstanceObjectsOfARun, ACompilationUnitIsNoChildOfTheTop) {
  Run(kUnitItemBesideTop);
  EXPECT_EQ(
      FullNameOfChild(vpi_handle_by_name(VpiText("top"), nullptr), "$unit"),
      "");
}

TEST_F(InstanceObjectsOfARun, ACompilationUnitItemsFullNameUsesColons) {
  Run(kUnitItemBesideTop);
  vpiHandle it = vpi_iterate(vpiPackage, nullptr);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(FullNameOfChild(vpi_scan(it), "g"), "$unit::g");
}

constexpr const char* kTwoTimescales =
    "module sub; timeunit 1us; timeprecision 1ps; endmodule\n"
    "module top; timeunit 10ns; timeprecision 1ns; sub s(); endmodule\n";

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

TEST_F(InstanceObjectsOfARun, NoObjectHasTheSmallestPrecision) {
  Run(kTwoTimescales);
  EXPECT_EQ(vpi_get(vpiTimePrecision, nullptr), -12);
}

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
  EXPECT_EQ(vpi_get(vpiProtected, By("top.u0")), 0);
}

TEST(InstanceModel, AnInstanceOfAProtectedDefinitionIsProtected) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);
  VpiObject mod;
  mod.type = kVpiModule;
  mod.instance_facts.protected_definition = true;
  EXPECT_EQ(vpi_get(vpiProtected, VpiHandleOf(&mod)), 1);
  SetGlobalVpiContext(nullptr);
}

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
  EXPECT_STREQ(vpi_get_str(vpiLibrary, By("top.i")), "work");
  EXPECT_STREQ(vpi_get_str(vpiLibrary, By("top.p")), "work");
  EXPECT_STREQ(vpi_get_str(vpiLibrary, By("pk")), "");
  for (const char* name : {"top.i", "top.p", "pk"}) {
    EXPECT_STREQ(vpi_get_str(vpiConfig, By(name)), "") << name;
  }
}

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
