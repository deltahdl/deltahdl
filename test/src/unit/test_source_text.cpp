#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- Test helpers ---

namespace {

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string& src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

}  // namespace

// =============================================================================
// A.1.2 source_text ::= [ timeunits_declaration ] { description }
// =============================================================================

// Empty source text.
TEST(SourceText, EmptySourceText) {
  auto r = Parse("");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules.empty());
}

// Multiple descriptions in source text.
TEST(SourceText, MultipleDescriptions) {
  auto r = Parse(
      "module m1; endmodule\n"
      "interface ifc; endinterface\n"
      "program prg; endprogram\n"
      "package pkg; endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->packages.size(), 1u);
}

// =============================================================================
// A.1.2 description — all alternatives
// =============================================================================

// description: module_declaration
TEST(SourceText, DescriptionModule) {
  auto r = Parse("module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
}

// description: udp_declaration
TEST(SourceText, DescriptionUdp) {
  auto r = Parse(
      "primitive my_udp(output y, input a, input b);\n"
      "  table\n"
      "    0 0 : 0 ;\n"
      "    1 1 : 1 ;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->name, "my_udp");
}

// description: interface_declaration
TEST(SourceText, DescriptionInterface) {
  auto r = Parse("interface ifc; endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->name, "ifc");
}

// description: program_declaration
TEST(SourceText, DescriptionProgram) {
  auto r = Parse("program prg; endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->name, "prg");
}

// description: package_declaration
TEST(SourceText, DescriptionPackage) {
  auto r = Parse("package pkg; endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
}

// description: config_declaration
TEST(SourceText, DescriptionConfig) {
  auto r = Parse(
      "config cfg;\n"
      "  design work.top;\n"
      "  default liblist work;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->name, "cfg");
}

// description: class_declaration
TEST(SourceText, DescriptionClass) {
  auto r = Parse("class C; endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "C");
}

// description: checker_declaration
TEST(SourceText, DescriptionChecker) {
  auto r = Parse("checker chk; endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->name, "chk");
}

// =============================================================================
// A.1.2 bind_directive (§23.11)
// =============================================================================

// Form 1: bind target_scope bind_instantiation
TEST(SourceText, BindDirectiveBasic) {
  auto r = Parse("bind target_mod checker_mod chk_inst(.a(sig));\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  EXPECT_EQ(r.cu->bind_directives[0]->target, "target_mod");
  EXPECT_TRUE(r.cu->bind_directives[0]->target_instances.empty());
  ASSERT_NE(r.cu->bind_directives[0]->instantiation, nullptr);
  EXPECT_EQ(r.cu->bind_directives[0]->instantiation->inst_module,
            "checker_mod");
  EXPECT_EQ(r.cu->bind_directives[0]->instantiation->inst_name, "chk_inst");
}

// Form 1 with instance list: bind scope : inst1, inst2 instantiation
TEST(SourceText, BindDirectiveWithInstanceList) {
  auto r = Parse("bind dut : i1, i2 chk chk_i(.clk(clk));\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  EXPECT_EQ(r.cu->bind_directives[0]->target, "dut");
  ASSERT_EQ(r.cu->bind_directives[0]->target_instances.size(), 2u);
  EXPECT_EQ(r.cu->bind_directives[0]->target_instances[0], "i1");
  EXPECT_EQ(r.cu->bind_directives[0]->target_instances[1], "i2");
}

// Form 2: bind hierarchical_instance instantiation
TEST(SourceText, BindDirectiveHierarchical) {
  auto r = Parse("bind top.dut.u1 checker_mod chk(.a(sig));\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  EXPECT_EQ(r.cu->bind_directives[0]->target, "top.dut.u1");
}

// Bind with parameterized instantiation.
TEST(SourceText, BindDirectiveParameterized) {
  auto r = Parse("bind target_mod my_checker #(8) chk_i(.clk(clk));\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  auto* inst = r.cu->bind_directives[0]->instantiation;
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->inst_params.size(), 1u);
}

// Bind stores source location.
TEST(SourceText, BindDirectiveHasSourceLoc) {
  auto r = Parse("bind target_mod chk chk_i(.a(s));\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  EXPECT_NE(r.cu->bind_directives[0]->loc.line, 0u);
}

// Multiple bind directives.
TEST(SourceText, MultipleBindDirectives) {
  auto r = Parse(
      "bind mod1 chk1 c1(.a(s));\n"
      "bind mod2 chk2 c2(.a(s));\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 2u);
  EXPECT_EQ(r.cu->bind_directives[0]->target, "mod1");
  EXPECT_EQ(r.cu->bind_directives[1]->target, "mod2");
}

// Bind mixed with other top-level descriptions.
TEST(SourceText, BindMixedWithOtherDescriptions) {
  auto r = Parse(
      "module m; endmodule\n"
      "bind m checker_mod chk_i(.a(sig));\n"
      "package p; endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->bind_directives.size(), 1u);
  EXPECT_EQ(r.cu->packages.size(), 1u);
}

// =============================================================================
// A.1.2 module_declaration — all forms
// =============================================================================

// module_keyword ::= module | macromodule
TEST(SourceText, ModuleKeywordMacromodule) {
  auto r = Parse("macromodule m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
}

// Module with lifetime qualifier: module automatic m;
TEST(SourceText, ModuleWithLifetime) {
  auto r = Parse("module automatic m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
}

// Module with ANSI header (list_of_port_declarations).
TEST(SourceText, ModuleAnsiHeader) {
  auto r = Parse("module m(input logic a, output logic b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
}

// Module with non-ANSI header (list_of_ports).
TEST(SourceText, ModuleNonAnsiHeader) {
  auto r = Parse(
      "module m(a, b);\n"
      "  input a;\n"
      "  output b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
}

// Extern module declaration.
TEST(SourceText, ExternModule) {
  auto r = Parse("extern module m(input logic a);\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->is_extern);
}

// Module with end label: endmodule : m
TEST(SourceText, ModuleEndLabel) {
  auto r = Parse("module m; endmodule : m\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
}

// =============================================================================
// A.1.2 interface_declaration — all forms
// =============================================================================

// Interface with lifetime.
TEST(SourceText, InterfaceWithLifetime) {
  auto r = Parse("interface automatic ifc; endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
}

// Interface with end label.
TEST(SourceText, InterfaceEndLabel) {
  auto r = Parse("interface ifc; endinterface : ifc\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.1.2 program_declaration — all forms
// =============================================================================

// Program with lifetime.
TEST(SourceText, ProgramWithLifetime) {
  auto r = Parse("program automatic prg; endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
}

// Program with end label.
TEST(SourceText, ProgramEndLabel) {
  auto r = Parse("program prg; endprogram : prg\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.1.2 package_declaration — with optional lifetime
// =============================================================================

// Package with automatic lifetime (A.1.2 gap fix).
TEST(SourceText, PackageAutomaticLifetime) {
  auto r = Parse("package automatic pkg; endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
}

// Package with static lifetime.
TEST(SourceText, PackageStaticLifetime) {
  auto r = Parse("package static pkg; endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
}

// Package with end label.
TEST(SourceText, PackageEndLabel) {
  auto r = Parse("package pkg; endpackage : pkg\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// Package with items and lifetime.
TEST(SourceText, PackageLifetimeWithItems) {
  auto r = Parse(
      "package automatic pkg;\n"
      "  parameter int W = 8;\n"
      "  typedef logic [W-1:0] word_t;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
  EXPECT_EQ(r.cu->packages[0]->items.size(), 2u);
}

// =============================================================================
// A.1.2 checker_declaration
// =============================================================================

// Checker with ports.
TEST(SourceText, CheckerWithPorts) {
  auto r = Parse("checker chk(event clk); endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->name, "chk");
}

// Checker with end label.
TEST(SourceText, CheckerEndLabel) {
  auto r = Parse("checker chk; endchecker : chk\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.1.2 class_declaration
// =============================================================================

// Virtual class.
TEST(SourceText, VirtualClass) {
  auto r = Parse("virtual class C; endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_TRUE(r.cu->classes[0]->is_virtual);
}

// Class with extends.
TEST(SourceText, ClassWithExtends) {
  auto r = Parse("class Child extends Parent; endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->base_class, "Parent");
}

// Class with parameters.
TEST(SourceText, ClassWithParams) {
  auto r = Parse("class C #(type T = int); endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->params.size(), 1u);
}

// Class with end label.
TEST(SourceText, ClassEndLabel) {
  auto r = Parse("class C; endclass : C\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.1.2 timeunits_declaration — all 4 forms
// =============================================================================

// Form 1: timeunit time_literal ;
TEST(SourceText, TimeunitOnly) {
  auto r = Parse("module m; timeunit 1ns; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->has_timeunit);
}

// Form 2: timeprecision time_literal ;
TEST(SourceText, TimeprecisionOnly) {
  auto r = Parse("module m; timeprecision 1ps; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->has_timeprecision);
}

// Form 3: timeunit time_literal / time_literal ;
TEST(SourceText, TimeunitWithSlash) {
  auto r = Parse("module m; timeunit 1ns / 1ps; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->has_timeunit);
  EXPECT_TRUE(r.cu->modules[0]->has_timeprecision);
}

// Form 4: both timeunit and timeprecision separately.
TEST(SourceText, TimeunitAndTimeprecisionSeparate) {
  auto r = Parse(
      "module m;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->has_timeunit);
  EXPECT_TRUE(r.cu->modules[0]->has_timeprecision);
}

// =============================================================================
// A.1.2 comprehensive: all description types in one source text.
// =============================================================================

TEST(SourceText, AllDescriptionTypes) {
  auto r = Parse(
      "package pkg; endpackage\n"
      "module m; endmodule\n"
      "interface ifc; endinterface\n"
      "program prg; endprogram\n"
      "class C; endclass\n"
      "checker chk; endchecker\n"
      "primitive my_udp(output y, input a);\n"
      "  table 0 : 0 ; 1 : 1 ; endtable\n"
      "endprimitive\n"
      "config cfg;\n"
      "  design work.m;\n"
      "  default liblist work;\n"
      "endconfig\n"
      "bind m chk chk_i(.a(s));\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->bind_directives.size(), 1u);
}
