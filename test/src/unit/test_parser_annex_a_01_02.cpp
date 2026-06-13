#include "fixture_parser.h"
#include "fixture_program.h"

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

TEST(SourceText, ClassDecl) {
  auto r = Parse(
      "class Packet;\n"
      "  rand bit [7:0] payload;\n"
      "  function void display();\n"
      "    $display(\"pkt\");\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "Packet");
  EXPECT_EQ(r.cu->classes[0]->members.size(), 2u);
}

TEST(SourceText, EmptyCuCompletelyEmpty) {
  auto r = Parse("");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.cu->modules.empty());
}

TEST(SourceText, CheckerDecl) {
  auto r = Parse(
      "checker my_chk(input clk, input rst);\n"
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

TEST(SourceText, PackageDecl) {
  auto r = Parse(
      "package my_pkg;\n"
      "  typedef int myint;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "my_pkg");
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

// description's bind_directive alternative: a bind directive may appear directly
// as a top-level description, landing in the compilation unit's bind list.
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

// interface_ansi_header: an interface whose ports carry directions in the header.
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

TEST(SourceText, ErrorUnknownTopLevelToken) {
  auto r = Parse("foobar;\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(SourceText, ErrorMissingEndpackage) {
  auto r = Parse("package pkg;\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(SourceText, ErrorMissingEndclass) {
  auto r = Parse("class C;\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(SourceText, ErrorMissingEndmodule) {
  auto r = Parse("module m;\n");
  EXPECT_TRUE(r.has_errors);
}

}
