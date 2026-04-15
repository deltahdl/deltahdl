#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ModuleHeaderDefinition, StaticModuleLifetime) {
  EXPECT_TRUE(
      ParseOk("module static m;\n"
              "  function int fn();\n"
              "    return 0;\n"
              "  endfunction\n"
              "endmodule\n"));
}

TEST(ModuleAndHierarchyParsing, EndLabelModule) {
  auto r = Parse("module foo; endmodule : foo\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  EXPECT_EQ(r.cu->modules[0]->name, "foo");
}

TEST(ModuleAndHierarchyParsing, EndLabelModuleNoLabel) {
  auto r = Parse("module bar; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  EXPECT_EQ(r.cu->modules[0]->name, "bar");
}

TEST(ModuleAndHierarchyParsing, ModuleHeaderImport) {
  auto r = Parse(
      "module m import pkg::*; ();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "m");

  ASSERT_GE(mod->items.size(), 1);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kImportDecl);
}

TEST(ModuleAndHierarchyParsing, ModuleHeaderImportDetails) {
  auto r = Parse(
      "module m import pkg::*; ();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 1);
  EXPECT_EQ(mod->items[0]->import_item.package_name, "pkg");
  EXPECT_TRUE(mod->items[0]->import_item.is_wildcard);
}

TEST(ModuleAndHierarchyParsing, ModuleHeaderImportWithParamsImport) {
  auto r = Parse(
      "module m import A::*; #(parameter N = 4) (input logic clk);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "m");
  ASSERT_GE(mod->items.size(), 1);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kImportDecl);
}

TEST(ModuleAndHierarchyParsing, ModuleHeaderImportWithParamsPortsAndParams) {
  auto r = Parse(
      "module m import A::*; #(parameter N = 4) (input logic clk);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->params.size(), 1);
  ASSERT_EQ(mod->ports.size(), 1);
}

TEST(ModuleAndHierarchyParsing, ModuleHeaderMultipleImportsFirst) {
  auto r = Parse(
      "module m import A::*, B::foo; ();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "m");
  ASSERT_GE(mod->items.size(), 2);
  EXPECT_EQ(mod->items[0]->import_item.package_name, "A");
  EXPECT_TRUE(mod->items[0]->import_item.is_wildcard);
}

TEST(ModuleAndHierarchyParsing, ModuleDefinitionEmpty) {
  auto r = Parse("module empty_mod; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  EXPECT_EQ(r.cu->modules[0]->name, "empty_mod");
  EXPECT_TRUE(r.cu->modules[0]->ports.empty());
  EXPECT_TRUE(r.cu->modules[0]->items.empty());
}
TEST(ModuleHeaderDefinition, ModuleLifetimeAutomatic) {
  auto r = Parse("module automatic t; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "t");
}

TEST(ModuleHeaderDefinition, TrailingSemicolonAfterEndmodule) {
  EXPECT_TRUE(ParseOk("module m; endmodule;"));
}

TEST(ModuleHeaderDefinition, ModuleNoPortList) {
  auto r = Parse("module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
  EXPECT_TRUE(r.cu->modules[0]->ports.empty());
}

TEST(ModuleDefinition, Mux2to1WithAnsiPorts) {
  auto r = Parse(
      "module mux2to1 (input wire a, b, sel,\n"
      "                output logic y);\n"
      "  always_comb begin\n"
      "    if (sel) y = a;\n"
      "    else     y = b;\n"
      "  end\n"
      "endmodule: mux2to1\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "mux2to1");
  EXPECT_FALSE(r.cu->modules[0]->ports.empty());
  EXPECT_FALSE(r.cu->modules[0]->items.empty());
}

TEST(ModuleDefinition, ModuleWithParamsPortsAndBody) {
  EXPECT_TRUE(ParseOk(
      "module m #(parameter int W = 8) (input logic clk, output logic [W-1:0] "
      "q);\n"
      "  typedef logic [W-1:0] data_t;\n"
      "  wire [W-1:0] net;\n"
      "  logic [W-1:0] var;\n"
      "  localparam int HALF = W / 2;\n"
      "  function automatic data_t invert(data_t d); return ~d; endfunction\n"
      "  assign net = var;\n"
      "  always_comb var = invert(q);\n"
      "  always_ff @(posedge clk) q <= net;\n"
      "endmodule\n"));
}

TEST(ModuleHeaderDefinition, ModuleWildcardPorts) {
  auto r = Parse("module m(.*); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->has_wildcard_ports);
}

TEST(ModuleHeaderDefinition, ExternModuleDecl) {
  auto r = Parse("extern module m(input a, output b);\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->is_extern);
}

TEST(ModuleHeaderDefinition, ModuleAnsiHeader) {
  auto r = Parse("module m(input logic a, output logic b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports.size(), 2u);
}

TEST(ModuleHeaderDefinition, ModuleNonAnsiHeader) {
  auto r = Parse(
      "module m(a, b);\n"
      "  input a;\n"
      "  output b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports.size(), 2u);
}

TEST(ModuleHeaderDefinition, ModuleStaticLifetime) {
  auto r = Parse("module static m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ModuleHeaderDefinition, ModuleWithLifetime) {
  auto r = Parse("module automatic m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ModuleHeaderDefinition, ModuleWithAttributes) {
  auto r = Parse("(* synthesis *) module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.cu->modules[0]->attrs.empty());
}

TEST(ModuleHeaderDefinition, TimeunitWithPrecisionSlash) {
  auto r = Parse(
      "module m;\n"
      "  timeunit 1ns / 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ModuleHeaderDefinition, TimeprecisionOnly) {
  auto r = Parse(
      "module m;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ModuleHeaderDefinition, TimeprecisionThenTimeunit) {
  auto r = Parse(
      "module m;\n"
      "  timeprecision 1ps;\n"
      "  timeunit 1ns;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ModuleParametersAndPorts, PortListVariantForms) {
  auto r1 = Parse("module m (); endmodule\n");
  ASSERT_NE(r1.cu, nullptr);
  EXPECT_FALSE(r1.has_errors);
  EXPECT_EQ(r1.cu->modules[0]->ports.size(), 0u);
  auto r2 = Parse("module m; endmodule\n");
  ASSERT_NE(r2.cu, nullptr);
  EXPECT_FALSE(r2.has_errors);
  EXPECT_EQ(r2.cu->modules[0]->ports.size(), 0u);
  EXPECT_TRUE(ParseOk("module m (.*); endmodule\n"));
  EXPECT_TRUE(ParseOk("module m (input int x = 10); endmodule\n"));

  EXPECT_TRUE(ParseOk("module m (input var int in1); endmodule\n"));
  EXPECT_TRUE(ParseOk("module m (output reg [7:0] q); endmodule\n"));
  EXPECT_TRUE(ParseOk("module m (input signed [7:0] s); endmodule\n"));

  EXPECT_TRUE(ParseOk("macromodule mm; endmodule\n"));
}

TEST(ModuleParametersAndPorts, EmptyParamPortList) {
  auto r = Parse("module m #(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->params.empty());
}

TEST(ModuleParametersAndPorts, ParamOmitValueInPortList) {
  auto r = Parse(
      "module m #(parameter int W) (input [W-1:0] d);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ModuleParametersAndPorts, TypeParamOmitTypeInPortList) {
  auto r = Parse(
      "module m #(parameter type T) ();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ModuleParametersAndPorts, BareDataTypeParamDecl) {
  auto r = Parse("module m #(parameter int A = 1, int B = 2)(); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->params.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->params[0].first, "A");
  EXPECT_EQ(r.cu->modules[0]->params[1].first, "B");
}

TEST(ModuleParametersAndPorts, TypeParamNoKeyword) {
  auto r = Parse("module m #(type T = int)(); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->params.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->params[0].first, "T");
}

TEST(ModuleParametersAndPorts, MixedParamPortDecls) {
  auto r = Parse(
      "module m #(parameter int A = 1, localparam int B = 5, type T = logic)\n"
      "(); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->params.size(), 3u);
}

TEST(ModuleParametersAndPorts, ErrorMissingPortListClose) {
  EXPECT_FALSE(ParseOk("module m(input logic a endmodule"));
}

TEST(ModuleParametersAndPorts, ErrorMissingParamListClose) {
  EXPECT_FALSE(ParseOk("module m #(parameter int W endmodule"));
}

TEST(ModuleParametersAndPorts, ErrorTrailingCommaInPortList) {
  EXPECT_FALSE(ParseOk("module m(input a,); endmodule"));
}

TEST(ModuleParametersAndPorts, ErrorTrailingCommaInParamList) {
  EXPECT_FALSE(ParseOk("module m #(parameter int A,)(); endmodule"));
}

TEST(ModuleHeaderDefinition, TimeunitsInModule) {
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

TEST(ModuleHeaderDefinition, ImportInHeaderFollowedByPorts) {
  auto r = Parse(
      "module m import pkg::*; (input a, output b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports.size(), 2u);
}

TEST(ModuleHeaderDefinition, ImportInHeaderFollowedByParams) {
  auto r = Parse(
      "module m import pkg::*; #(parameter int W = 8) (input a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ModuleHeaderDefinition, ImportInHeaderFollowedByBoth) {
  auto r = Parse(
      "module m import pkg::*; #(parameter int W = 8) (input a, output b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ModuleAndHierarchyParsing, ExternModuleHeader) {
  auto r = Parse("extern module foo(input logic a, output logic b);\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "foo");
  EXPECT_TRUE(mod->is_extern);
  EXPECT_TRUE(mod->items.empty());
}

TEST(ModuleAndHierarchyParsing, ExternModulePorts) {
  auto r = Parse("extern module foo(input logic a, output logic b);\n");
  VerifyTwoPortModule(r, "a", Direction::kInput, "b", Direction::kOutput);
}

TEST(ModuleAndHierarchyParsing, ExternModuleNoBody) {
  auto r = Parse(
      "extern module bar(input logic x);\n"
      "module baz; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 2);
  struct Expected {
    const char* name;
    bool is_extern;
  };
  Expected expected[] = {{"bar", true}, {"baz", false}};
  for (size_t i = 0; i < 2; ++i) {
    EXPECT_EQ(r.cu->modules[i]->name, expected[i].name);
    EXPECT_EQ(r.cu->modules[i]->is_extern, expected[i].is_extern);
  }
}

TEST(ModuleAndHierarchyParsing, ExternModuleNonAnsiPorts) {
  auto r = Parse("extern module m (a, b, c);\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "m");
  EXPECT_TRUE(mod->is_extern);
  EXPECT_TRUE(mod->items.empty());
}

TEST(ModuleAndHierarchyParsing, ExternModuleWithParams) {
  auto r = Parse(
      "extern module a #(parameter size = 8)\n"
      "  (input [size:0] x, output logic y);\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "a");
  EXPECT_TRUE(mod->is_extern);
  ASSERT_EQ(mod->params.size(), 1);
  EXPECT_EQ(mod->params[0].first, "size");
  ASSERT_EQ(mod->ports.size(), 2);
}

TEST(ModuleAndHierarchyParsing, ExternModuleFollowedByDefinition) {
  auto r = Parse(
      "extern module ext (input a, output b);\n"
      "module other (input x);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 2);
  EXPECT_EQ(r.cu->modules[0]->name, "ext");
  EXPECT_TRUE(r.cu->modules[0]->is_extern);
  EXPECT_EQ(r.cu->modules[1]->name, "other");
  EXPECT_FALSE(r.cu->modules[1]->is_extern);
}

TEST(ModuleAndHierarchyParsing, ModuleHeaderMultipleImportsSecond) {
  auto r = Parse(
      "module m import A::*, B::foo; ();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 2);
  EXPECT_EQ(mod->items[1]->import_item.package_name, "B");
  EXPECT_EQ(mod->items[1]->import_item.item_name, "foo");
}

TEST(ModuleHeaderDefinition, TimeunitOnly) {
  auto r = Parse(
      "module m;\n"
      "  timeunit 1ns;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->has_timeunit);
  EXPECT_FALSE(r.cu->modules[0]->has_timeprecision);
}

TEST(ModuleHeaderDefinition, EndLabelMismatchIsError) {
  EXPECT_FALSE(ParseOk("module m; endmodule : wrong\n"));
}

TEST(ModuleHeaderDefinition, NonAnsiHeaderWithImport) {
  auto r = Parse(
      "module m import pkg::*; (a);\n"
      "  input a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ModuleHeaderDefinition, ExternMacromodule) {
  auto r = Parse("extern macromodule m(input logic a);\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->is_extern);
}

TEST(ModuleHeaderDefinition, ExternWithLifetime) {
  auto r = Parse("extern module automatic m(input logic a);\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->is_extern);
  EXPECT_TRUE(r.cu->modules[0]->is_automatic);
}

TEST(ModuleHeaderDefinition, ExternAnsiEmptyPortList) {
  auto r = Parse("extern module m();\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->is_extern);
  EXPECT_TRUE(r.cu->modules[0]->ports.empty());
}

TEST(ModuleHeaderDefinition, LifetimeWithAttributes) {
  auto r = Parse("(* synthesis *) module automatic m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->modules[0]->attrs.empty());
  EXPECT_TRUE(r.cu->modules[0]->is_automatic);
}

TEST(ModuleHeaderDefinition, MultipleAttributeInstances) {
  auto r = Parse("(* a = 1 *) (* b = 2 *) module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_GE(r.cu->modules[0]->attrs.size(), 2u);
}

TEST(ModuleHeaderDefinition, WildcardPortsWithLifetime) {
  auto r = Parse("module automatic m(.*); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->has_wildcard_ports);
  EXPECT_TRUE(r.cu->modules[0]->is_automatic);
}

TEST(ModuleHeaderDefinition, WildcardPortsWithTimeunits) {
  auto r = Parse(
      "module m(.*);\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->has_wildcard_ports);
  EXPECT_TRUE(r.cu->modules[0]->has_timeunit);
}

TEST(ModuleHeaderDefinition, WildcardPortsWithAttributes) {
  auto r = Parse("(* keep *) module m(.*); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->has_wildcard_ports);
  EXPECT_FALSE(r.cu->modules[0]->attrs.empty());
}

TEST(ModuleHeaderDefinition, IsAutomaticSetForAutomatic) {
  auto r = Parse("module automatic m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.cu->modules[0]->is_automatic);
}

TEST(ModuleHeaderDefinition, IsAutomaticFalseByDefault) {
  auto r = Parse("module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.cu->modules[0]->is_automatic);
}

TEST(ModuleHeaderDefinition, IsAutomaticFalseForStatic) {
  auto r = Parse("module static m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.cu->modules[0]->is_automatic);
}

TEST(ModuleParametersAndPorts, HasParamPortListSetWhenPresent) {
  auto r = Parse("module m #(parameter int W = 8)(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.cu->modules[0]->has_param_port_list);
}

TEST(ModuleParametersAndPorts, HasParamPortListFalseWhenAbsent) {
  auto r = Parse("module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.cu->modules[0]->has_param_port_list);
}

TEST(ModuleParametersAndPorts, SharedParameterKeyword) {
  auto r = Parse("module m #(parameter W = 8, D = 4)(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->params.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->params[0].first, "W");
  EXPECT_EQ(r.cu->modules[0]->params[1].first, "D");
}

TEST(ModuleHeaderDefinition, NonAnsiWithParamsAndImport) {
  auto r = Parse(
      "module m import pkg::*; #(parameter int N = 1)(a, b);\n"
      "  input a;\n"
      "  output b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->params.size(), 1u);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
}

TEST(ModuleHeaderDefinition, MacromoduleAnsiHeader) {
  auto r = Parse("macromodule m(input logic a, output logic b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports.size(), 2u);
}

TEST(ModuleHeaderDefinition, MacromoduleWithLifetime) {
  auto r = Parse("macromodule automatic m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->is_automatic);
}

TEST(ModuleHeaderDefinition, WildcardPortsEndLabel) {
  auto r = Parse("module m(.*); endmodule : m\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->has_wildcard_ports);
}

TEST(ModuleHeaderDefinition, ExternAnsiWithAttributes) {
  auto r = Parse("(* keep *) extern module m(input logic a);\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->is_extern);
  EXPECT_FALSE(r.cu->modules[0]->attrs.empty());
}

TEST(ModuleHeaderDefinition, ErrorMissingEndmodule) {
  EXPECT_FALSE(ParseOk("module m;\n"));
}

TEST(ModuleHeaderDefinition, ErrorMissingModuleName) {
  EXPECT_FALSE(ParseOk("module ; endmodule\n"));
}

TEST(ModuleHeaderDefinition, ErrorMissingSemicolonAfterHeader) {
  EXPECT_FALSE(ParseOk("module m endmodule\n"));
}

}  // namespace
