#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

TEST_F(ConfigParseTest, MultipleConfigs) {
  auto* unit = Parse(R"(
    config cfg1;
      design lib.top1;
    endconfig
    config cfg2;
      design lib.top2;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 2u);
  EXPECT_EQ(unit->configs[0]->name, "cfg1");
  EXPECT_EQ(unit->configs[1]->name, "cfg2");
}

TEST(SourceText, EmptyCuCompletelyEmpty) {
  auto r = Parse("");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.cu->modules.empty());
}

TEST(SourceText, CheckerDecl) {
  auto r = Parse(
      "checker my_chk(input logic clk, input logic rst);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->name, "my_chk");
}

TEST(SourceText, CheckerDeclEndLabel) {
  auto r = Parse("checker chk; endchecker : chk\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SourceText, PackageDeclEndLabel) {
  auto r = Parse("package p; endpackage : p\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SourceText, TimeunitsDeclaration) {
  auto r = Parse(
      "timeunit 1ns;\n"
      "timeprecision 1ps;\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// timeunits_declaration's combined form: a single timeunit statement may carry
// the precision after a slash, setting both the unit and the precision at once.
TEST(SourceText, TimeunitWithPrecisionRatio) {
  auto r = Parse("timeunit 1ns / 1ps;\nmodule m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->has_cu_timeunit);
  EXPECT_TRUE(r.cu->has_cu_timeprecision);
  EXPECT_EQ(r.cu->cu_time_unit, TimeUnit::kNs);
  EXPECT_EQ(r.cu->cu_time_prec, TimeUnit::kPs);
}

TEST(SourceText, DescriptionClass) {
  auto r = Parse("class C; endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "C");
}

TEST(SourceText, DescriptionChecker) {
  auto r = Parse("checker chk; endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->name, "chk");
}

TEST(SourceText, DescriptionPackage) {
  auto r = Parse("package pkg; endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
}

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

// description's bind_directive alternative: a bind directive may appear
// directly as a top-level description, landing in the compilation unit's bind
// list.
TEST(SourceText, DescriptionBindDirective) {
  auto r = Parse("bind target_mod chk chk_i(.a(s));\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->bind_directives.size(), 1u);
}

TEST(SourceText, CheckerDeclWithParens) {
  auto r = Parse("checker chk(); endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
}

TEST(SourceText, PackageWithLifetime) {
  auto r = Parse("package automatic pkg; endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

// module_ansi_header: ports are declared with directions in the header itself,
// distinguishing it from the non-ansi header form exercised by ModuleDecl.
TEST(SourceText, ModuleAnsiHeader) {
  auto r = Parse("module m(input a, output b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInput);
  EXPECT_EQ(r.cu->modules[0]->ports[1].direction, Direction::kOutput);
  EXPECT_FALSE(r.cu->modules[0]->is_non_ansi_ports);
}

// module_keyword's second alternative: macromodule is accepted wherever module
// is, producing the same module declaration.
TEST(SourceText, MacromoduleKeyword) {
  auto r = Parse("macromodule m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
}

// interface_ansi_header: an interface whose ports carry directions in the
// header.
TEST(SourceText, InterfaceAnsiHeader) {
  auto r = Parse("interface ifc(input clk); endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  ASSERT_EQ(r.cu->interfaces[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->ports[0].direction, Direction::kInput);
}

// program_ansi_header: a program whose ports carry directions in the header.
TEST(SourceText, ProgramAnsiHeader) {
  auto r = Parse("program prg(input clk); endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  ASSERT_EQ(r.cu->programs[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->ports[0].direction, Direction::kInput);
}

// interface_class_declaration: 'interface class' yields a class flagged as an
// interface class, distinct from an ordinary class_declaration.
TEST(SourceText, InterfaceClassDecl) {
  auto r = Parse("interface class IC; endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "IC");
  EXPECT_TRUE(r.cu->classes[0]->is_interface);
}

// module_nonansi_header: a port list of bare identifiers (no directions) marks
// the declaration non-ansi, the counterpart to the ansi header form.
TEST(SourceText, ModuleNonAnsiHeaderPorts) {
  auto r = Parse("module m(a, b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->is_non_ansi_ports);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kNone);
}

// module_declaration's (.*) form: an implicit-port module header.
TEST(SourceText, ModuleWildcardPorts) {
  auto r = Parse("module m(.*); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->has_wildcard_ports);
}

// module_declaration's optional end label: endmodule may be followed by the
// module identifier.
TEST(SourceText, ModuleEndLabel) {
  auto r = Parse("module m; endmodule : m\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

// module_declaration's extern alternative: an extern module header has no body
// and records the module as extern.
TEST(SourceText, ExternModuleHeader) {
  auto r = Parse("extern module m(input a, output b);\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->is_extern);
}

// interface_declaration's extern alternative.
TEST(SourceText, ExternInterfaceHeader) {
  auto r = Parse("extern interface ifc(input a);\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_TRUE(r.cu->interfaces[0]->is_extern);
}

// program_declaration's extern alternative.
TEST(SourceText, ExternProgramHeader) {
  auto r = Parse("extern program prg(input a);\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(r.cu->programs[0]->is_extern);
}

// class_declaration's leading 'virtual' option: the class is flagged virtual.
TEST(SourceText, VirtualClass) {
  auto r = Parse("virtual class C; endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_TRUE(r.cu->classes[0]->is_virtual);
}

// class_declaration's final_specifier option: ': final' before the identifier
// marks the class as final.
TEST(SourceText, FinalClass) {
  auto r = Parse("class : final C; endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_TRUE(r.cu->classes[0]->is_final);
}

// class_declaration's optional parameter_port_list: a parameterized class
// records its parameters.
TEST(SourceText, ParameterizedClass) {
  auto r = Parse("class C #(parameter int W = 8); endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_FALSE(r.cu->classes[0]->params.empty());
}

// class_declaration's 'extends class_type' option: the base class name is
// recorded.
TEST(SourceText, ClassExtends) {
  auto r = Parse("class D extends B; endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->base_class, "B");
}

// class_declaration's 'extends class_type ( list_of_arguments )' option: the
// base constructor argument list is captured.
TEST(SourceText, ClassExtendsWithArgs) {
  auto r = Parse("class D extends B(1); endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->extends_args.size(), 1u);
}

// class_declaration's 'extends class_type ( default )' option: the 'default'
// argument marker is recorded distinctly from a positional argument list.
TEST(SourceText, ClassExtendsDefaultArgs) {
  auto r = Parse("class D extends B(default); endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_TRUE(r.cu->classes[0]->extends_has_default);
}

// class_declaration's 'implements interface_class_type' option: implemented
// interface classes are recorded.
TEST(SourceText, ClassImplements) {
  auto r = Parse("class C implements I; endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->implements_types.size(), 1u);
}

// class_declaration's optional 'endclass : class_identifier' end label.
TEST(SourceText, ClassEndLabel) {
  auto r = Parse("class C; endclass : C\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

// interface_class_declaration's 'extends interface_class_type' option: an
// interface class extending a base interface class records its base.
TEST(SourceText, InterfaceClassExtends) {
  auto r = Parse("interface class IC extends IB; endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_TRUE(r.cu->classes[0]->is_interface);
  EXPECT_EQ(r.cu->classes[0]->base_class, "IB");
}

// interface_nonansi_header: an interface whose port list is bare identifiers
// (no directions) is the non-ansi header counterpart to InterfaceAnsiHeader.
TEST(SourceText, InterfaceNonAnsiHeaderPorts) {
  auto r = Parse("interface ifc(a, b); endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_TRUE(r.cu->interfaces[0]->is_non_ansi_ports);
}

// interface_declaration's (.*) form: an interface with an implicit port list.
TEST(SourceText, InterfaceWildcardPorts) {
  auto r = Parse("interface ifc(.*); endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_TRUE(r.cu->interfaces[0]->has_wildcard_ports);
}

// interface_declaration's optional 'endinterface : interface_identifier' label.
TEST(SourceText, InterfaceEndLabel) {
  auto r = Parse("interface ifc; endinterface : ifc\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
}

// program_nonansi_header: a program whose port list is bare identifiers.
TEST(SourceText, ProgramNonAnsiHeaderPorts) {
  auto r = Parse("program prg(a, b); endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(r.cu->programs[0]->is_non_ansi_ports);
}

// program_declaration's (.*) form: a program with an implicit port list.
TEST(SourceText, ProgramWildcardPorts) {
  auto r = Parse("program prg(.*); endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(r.cu->programs[0]->has_wildcard_ports);
}

// program_declaration's optional 'endprogram : program_identifier' label.
TEST(SourceText, ProgramEndLabel) {
  auto r = Parse("program prg; endprogram : prg\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
}

// module_declaration's 'extern module_nonansi_header' alternative: an extern
// header whose bare-identifier port list marks it non-ansi.
TEST(SourceText, ExternModuleNonAnsiHeader) {
  auto r = Parse("extern module m(a, b);\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->is_extern);
  EXPECT_TRUE(r.cu->modules[0]->is_non_ansi_ports);
}

// interface_declaration's 'extern interface_nonansi_header' alternative: the
// non-ansi (bare-identifier ports) counterpart to ExternInterfaceHeader.
TEST(SourceText, ExternInterfaceNonAnsiHeader) {
  auto r = Parse("extern interface ifc(a, b);\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_TRUE(r.cu->interfaces[0]->is_extern);
  EXPECT_TRUE(r.cu->interfaces[0]->is_non_ansi_ports);
}

// program_declaration's 'extern program_nonansi_header' alternative: the
// non-ansi counterpart to ExternProgramHeader.
TEST(SourceText, ExternProgramNonAnsiHeader) {
  auto r = Parse("extern program prg(a, b);\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(r.cu->programs[0]->is_extern);
  EXPECT_TRUE(r.cu->programs[0]->is_non_ansi_ports);
}

// timeunits_declaration's fourth form: timeprecision followed by timeunit as a
// pair, the reverse ordering of TimeunitsDeclaration.
TEST(SourceText, TimeprecisionThenTimeunit) {
  auto r = Parse(
      "timeprecision 1ps;\n"
      "timeunit 1ns;\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// module_nonansi_header's optional lifetime: 'automatic' before the identifier
// records the module's lifetime.
TEST(SourceText, ModuleLifetime) {
  auto r = Parse("module automatic m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->is_automatic);
}

// interface_nonansi_header's optional lifetime.
TEST(SourceText, InterfaceLifetime) {
  auto r = Parse("interface automatic ifc; endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_TRUE(r.cu->interfaces[0]->is_automatic);
}

// program_nonansi_header's optional lifetime.
TEST(SourceText, ProgramLifetime) {
  auto r = Parse("program automatic prg; endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(r.cu->programs[0]->is_automatic);
}

// module_ansi_header's optional parameter_port_list: a '#(...)' parameter port
// list is recorded on the module.
TEST(SourceText, ModuleParameterPortList) {
  auto r = Parse("module m #(parameter int W = 8); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->has_param_port_list);
  EXPECT_FALSE(r.cu->modules[0]->params.empty());
}

// interface_ansi_header's optional parameter_port_list.
TEST(SourceText, InterfaceParameterPortList) {
  auto r = Parse("interface ifc #(parameter int W = 8); endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_TRUE(r.cu->interfaces[0]->has_param_port_list);
  EXPECT_FALSE(r.cu->interfaces[0]->params.empty());
}

// program_ansi_header's optional parameter_port_list.
TEST(SourceText, ProgramParameterPortList) {
  auto r = Parse("program prg #(parameter int W = 8); endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(r.cu->programs[0]->has_param_port_list);
  EXPECT_FALSE(r.cu->programs[0]->params.empty());
}

// module_ansi_header's '{ package_import_declaration }': a package import may
// precede the port list in the header; it is recorded as a header import item.
// Built from real §A.1.11 import syntax against a genuine package.
TEST(SourceText, ModuleHeaderPackageImport) {
  auto r = Parse(
      "package p; typedef int t; endpackage\n"
      "module m import p::*; (); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  bool found_header_import = false;
  for (auto* it : r.cu->modules[0]->items) {
    if (it->kind == ModuleItemKind::kImportDecl && it->import_item.is_header)
      found_header_import = true;
  }
  EXPECT_TRUE(found_header_import);
}

// module_nonansi_header's leading '{ attribute_instance }': an attribute
// instance may precede a top-level module declaration and is attached to it.
TEST(SourceText, ModuleAttributeInstance) {
  auto r = Parse("(* keep *) module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.cu->modules[0]->attrs.empty());
}

// module_declaration's optional inner timeunits_declaration: a timeunit in the
// module body sets the module's time unit.
TEST(SourceText, ModuleBodyTimeunit) {
  auto r = Parse("module m; timeunit 1ns; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->has_timeunit);
}

// interface_declaration's optional inner timeunits_declaration.
TEST(SourceText, InterfaceBodyTimeunit) {
  auto r = Parse("interface ifc; timeunit 1ns; endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_TRUE(r.cu->interfaces[0]->has_timeunit);
}

// program_declaration's optional inner timeunits_declaration.
TEST(SourceText, ProgramBodyTimeunit) {
  auto r = Parse("program prg; timeunit 1ns; endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(r.cu->programs[0]->has_timeunit);
}

// package_declaration's optional inner timeunits_declaration.
TEST(SourceText, PackageBodyTimeunit) {
  auto r = Parse("package p; timeunit 1ns; endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_TRUE(r.cu->packages[0]->has_timeunit);
}

// Each of the six sources below runs out before its closing keyword, so
// Parser::Expect names that keyword and reports EOF. The end of a one-line
// source stands on line 2, the line the trailing newline opened.

TEST(SourceText, ErrorMissingEndinterface) {
  auto r = Parse("interface ifc;\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'endinterface', got EOF", 2, "25.3"));
}

TEST(SourceText, ErrorMissingEndprogram) {
  auto r = Parse("program prg;\n");
  // §24.6 gives the anonymous program, which this is not; the report over a
  // program declaration's missing `endprogram` is filed under §24.3.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'endprogram', got EOF", 2, "24.3"));
}

TEST(SourceText, ErrorMissingEndchecker) {
  auto r = Parse("checker chk;\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'endchecker', got EOF", 2, "17.2"));
}

TEST(SourceText, ErrorUnknownTopLevelToken) {
  auto r = Parse("foobar;\n");
  // §3.12.1 owns what may stand at the top of a compilation unit, and an
  // identifier alone is none of it.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected top-level declaration", 1, "3.12.1"));
}

TEST(SourceText, ErrorMissingEndpackage) {
  auto r = Parse("package pkg;\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'endpackage', got EOF", 2, "26.2"));
}

TEST(SourceText, ErrorMissingEndclass) {
  auto r = Parse("class C;\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected 'endclass', got EOF", 2, "8.3"));
}

TEST(SourceText, ErrorMissingEndmodule) {
  auto r = Parse("module m;\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'endmodule', got EOF", 2, "23.2"));
}

// --- timeunits_declaration gives the slash to `timeunit` alone:
// `timeunit time_literal [ / time_literal ] ;` against `timeprecision
// time_literal ;`, and §3.14.2.2 says which keyword the second argument
// belongs to: the time precision may also be given as an optional second,
// slash-separated argument of the timeunit keyword. ---

TEST(SourceText, TimeprecisionWithSlashIsRejectedInCompilationUnit) {
  auto r = Parse("timeprecision 1ns / 1ps;\nmodule m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags,
      "timeprecision takes one time literal; the slash form belongs to "
      "timeunit alone",
      1, "3.14.2.2"));
  // The precision before the slash is the one declared; the literal after it
  // sets nothing, and the unit in particular stays undeclared.
  EXPECT_TRUE(r.cu->has_cu_timeprecision);
  EXPECT_EQ(r.cu->cu_time_prec, TimeUnit::kNs);
  EXPECT_FALSE(r.cu->has_cu_timeunit);
}

TEST(SourceText, TimeprecisionWithSlashIsRejectedInModule) {
  auto r = Parse(
      "module m;\n"
      "  timeprecision 1ns / 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags,
      "timeprecision takes one time literal; the slash form belongs to "
      "timeunit alone",
      2, "3.14.2.2"));
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->has_timeprecision);
  EXPECT_EQ(r.cu->modules[0]->time_prec, TimeUnit::kNs);
  EXPECT_FALSE(r.cu->modules[0]->has_timeunit);
}

// The declaration is read to its semicolon, so what follows it is still read.
TEST(SourceText, TimeprecisionWithSlashIsReportedOnce) {
  auto r = Parse(
      "module m;\n"
      "  timeprecision 1ns / 1ps;\n"
      "  logic q;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags,
      "timeprecision takes one time literal; the slash form belongs to "
      "timeunit alone",
      2, "3.14.2.2"));
  EXPECT_EQ(r.diags.size(), 1u);
}

// A.1.2's ( .* ) forms of module_declaration, interface_declaration and
// program_declaration write nothing between the element's name and ( .* ),
// whose ports and parameters come from its extern declaration (§23.5), so a
// parameter port list or a package import before it is reported (#7544).
TEST(SourceText, AWildcardHeaderWritesNoParameterPortList) {
  auto r = Parse(
      "module m #(parameter int W = 1) (.*);\n"
      "endmodule\n"
      "program q #(parameter int N = 2) (.*);\n"
      "endprogram\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a ( .* ) header writes no parameter port list", 1, "A.1.2"));
  EXPECT_TRUE(ReportedError(
      r.diags, "a ( .* ) header writes no parameter port list", 3, "A.1.2"));
}

TEST(SourceText, AWildcardHeaderWritesNoPackageImport) {
  auto r = Parse(
      "package p; endpackage\n"
      "interface i import p::*; (.*);\n"
      "endinterface\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "a ( .* ) header writes no package import "
                            "declaration",
                            2, "A.1.2"));
}

// A.1.2: the ( .* ) header with nothing before it is still a module's.
TEST(SourceText, AWildcardHeaderAloneIsAccepted) {
  auto r = Parse(
      "module m(.*);\n"
      "endmodule\n");
  EXPECT_TRUE(r.diags.empty());
}

// A.1.2 writes an extern declaration with a non-ANSI or an ANSI header, and
// neither has the ( .* ) form (#7545).
TEST(SourceText, AnExternHeaderHasNoWildcardForm) {
  auto r = Parse(
      "extern module m(.*);\n"
      "extern interface i(.*);\n"
      "extern program q(.*);\n");
  for (int line = 1; line <= 3; ++line) {
    EXPECT_TRUE(ReportedError(
        r.diags, "an extern declaration's header has no ( .* ) form", line,
        "A.1.2"));
  }
}

// A.1.2 gives a lifetime to the ( .* ) form of a module alone (#7546).
TEST(SourceText, AWildcardInterfaceOrProgramHeaderTakesNoLifetime) {
  auto r = Parse(
      "interface automatic i(.*);\n"
      "endinterface\n"
      "program static q(.*);\n"
      "endprogram\n"
      "module automatic m(.*);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "an interface ( .* ) header takes no lifetime", 1, "A.1.2"));
  EXPECT_TRUE(ReportedError(
      r.diags, "a program ( .* ) header takes no lifetime", 3, "A.1.2"));
  EXPECT_EQ(r.diags.size(), 2u);
}

// A.1.2's checker_declaration writes the checker's name and an optional port
// list alone: no package import, no parameter port list and no ( .* ) (#7547).
TEST(SourceText, ACheckerHeaderWritesNoImportParametersOrWildcard) {
  auto r = Parse(
      "package p; endpackage\n"
      "checker c1 import p::*; (logic a);\n"
      "endchecker\n"
      "checker c2 #(parameter int N = 1) (logic a);\n"
      "endchecker\n"
      "checker c3(.*);\n"
      "endchecker\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "a checker header writes no package import "
                            "declaration",
                            2, "A.1.2"));
  EXPECT_TRUE(ReportedError(
      r.diags, "a checker header writes no parameter port list", 4, "A.1.2"));
  EXPECT_TRUE(ReportedError(r.diags, "a checker header has no ( .* ) form", 6,
                            "A.1.2"));
}

// A.1.2: a class's extends clause names one class type, and only an interface
// class's names a list (#7548).
TEST(SourceText, AClassExtendsOneClassType) {
  auto r = Parse(
      "class A; endclass\n"
      "class B; endclass\n"
      "class C extends A, B;\n"
      "endclass\n"
      "interface class I; endclass\n"
      "interface class J; endclass\n"
      "interface class K extends I, J;\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "a class extends one class type; only an interface "
                            "class extends several",
                            3, "A.1.2"));
  EXPECT_EQ(r.diags.size(), 1u);
}

// A.1.2: an interface class type in an implements clause takes no arguments,
// which were read and dropped unreported (#7549).
TEST(SourceText, AnImplementedInterfaceClassTakesNoArguments) {
  auto r = Parse(
      "interface class I; endclass\n"
      "class C implements I(1, 2);\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "an interface class type in an implements clause "
                            "takes no arguments",
                            2, "A.1.2"));
}

// A.1.2's interface_class_declaration writes no `virtual`, no final specifier
// and no arguments after an extended interface class type (#7550).
TEST(SourceText, AnInterfaceClassHeaderWritesNoClassOnlyParts) {
  auto r = Parse(
      "interface class J; endclass\n"
      "virtual interface class I1; endclass\n"
      "interface class : final I2; endclass\n"
      "interface class I3 extends J(1); endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "an interface class is not declared virtual", 2, "A.1.2"));
  EXPECT_TRUE(ReportedError(
      r.diags, "an interface class takes no final specifier", 3, "A.1.2"));
  EXPECT_TRUE(ReportedError(r.diags,
                            "an interface class type in an extends clause "
                            "takes no arguments",
                            4, "A.1.2"));
}

// A.1.2 writes each extern form as `extern` and a header, and every header
// opens with its own { attribute_instance }, so an extern declaration's
// attribute instances follow `extern`. There they had sent the parser skipping
// to the next ';', dropping the declaration unreported (#7993).
TEST(SourceText, AttributesAfterExternOpenTheHeader) {
  auto r = Parse(
      "extern (* keep *) module m(input a);\n"
      "extern (* keep *) interface i(input a);\n"
      "extern (* keep *) program q(input a);\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->is_extern);
  ASSERT_EQ(r.cu->modules[0]->attrs.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->attrs[0].name, "keep");
  EXPECT_EQ(r.cu->interfaces[0]->attrs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->attrs.size(), 1u);
}

// No production puts an attribute instance before `extern`; an extern
// declaration's stand after it, at the head of its header (#7995).
TEST(SourceText, AttributesBeforeExternAreRejected) {
  auto r = Parse(
      "(* keep *) extern module m(input a);\n"
      "(* keep *) extern primitive p(output y, input a);\n");
  const char* const kMsg =
      "an extern declaration's attribute instances are written after "
      "'extern', not before it";
  EXPECT_TRUE(ReportedError(r.diags, kMsg, 1, "A.1.2"));
  EXPECT_TRUE(ReportedError(r.diags, kMsg, 2, "A.1.2"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->udps.size(), 1u);
}

// At compilation-unit scope `description` reaches `extern` only through the
// extern headers of a module, interface, program or primitive. Any other token
// after it had been skipped to the next ';' unreported (#7994).
TEST(SourceText, ExternOpeningNoHeaderIsRejected) {
  auto r = Parse(
      "extern logic x;\n"
      "extern class C;\n"
      "module m; endmodule\n");
  const char* const kMsg =
      "the token after 'extern' opens no module, interface, program or "
      "primitive header";
  EXPECT_TRUE(ReportedError(r.diags, kMsg, 1, "A.1.2"));
  EXPECT_TRUE(ReportedError(r.diags, kMsg, 2, "A.1.2"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules.size(), 1u);
}

}  // namespace
