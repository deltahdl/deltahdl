// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

ModuleItem* FindModuleInst(const std::vector<ModuleItem*>& items) {
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kModuleInst) return item;
  }
  return nullptr;
}

RtlirDesign* Elaborate(const std::string& src, ElabFixture& f,
                       std::string_view top = "") {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  auto name = top.empty() ? cu->modules.back()->name : top;
  return elab.Elaborate(name);
}

namespace {

TEST(ParserAnnexA0411, ElaborationInstanceArray) {
  auto r = Parse(
      "module sub(input a, output b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  wire [3:0] x, y;\n"
      "  sub u0[3:0](.a(x), .b(y));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* inst = FindModuleInst(r.cu->modules[1]->items);
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->inst_name, "u0");
  EXPECT_NE(inst->inst_range_left, nullptr);
  EXPECT_NE(inst->inst_range_right, nullptr);
}

TEST(ParserAnnexA0411, ElaborationWildcardPortConnection) {
  auto r = Parse(
      "module sub(input a, output b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  wire a, b;\n"
      "  sub u0(.*);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* inst = FindModuleInst(r.cu->modules[1]->items);
  ASSERT_NE(inst, nullptr);
  EXPECT_TRUE(inst->inst_wildcard);
  EXPECT_EQ(inst->inst_ports.size(), 0u);
}

TEST(ParserAnnexA0411, MultipleInstancesSharedParams) {
  auto r = Parse(
      "module sub #(parameter W = 1)(input [W-1:0] d);\n"
      "endmodule\n"
      "module top;\n"
      "  sub #(.W(8)) u0(.d(8'd0)), u1(.d(8'd1));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[1]->items.size(), 2u);
  auto* i0 = r.cu->modules[1]->items[0];
  auto* i1 = r.cu->modules[1]->items[1];
  EXPECT_EQ(i0->inst_module, "sub");
  EXPECT_EQ(i0->inst_params.size(), 1u);
  EXPECT_EQ(i0->inst_params[0].first, "W");
  EXPECT_EQ(i1->inst_module, "sub");
  EXPECT_EQ(i1->inst_params.size(), 1u);
  EXPECT_EQ(i1->inst_params[0].first, "W");
}

// =============================================================================
// A.4.1.2 -- Interface instantiation
//
// interface_instantiation ::=
//   interface_identifier [ parameter_value_assignment ]
//     hierarchical_instance { , hierarchical_instance } ;
// =============================================================================
// --- interface_instantiation: basic ---
TEST(ParserAnnexA0412, BasicInterfaceInst) {
  auto r = Parse("module m; my_if u0(.a(a), .b(b)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "my_if");
  EXPECT_EQ(item->inst_name, "u0");
}

// --- interface_instantiation: with parameter_value_assignment ---
TEST(ParserAnnexA0412, InterfaceInstWithParams) {
  auto r = Parse("module m; my_if #(8) u0(.a(a)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "my_if");
  EXPECT_EQ(item->inst_name, "u0");
  ASSERT_EQ(item->inst_params.size(), 1u);
}

// --- interface_instantiation: with named parameter_value_assignment ---
TEST(ParserAnnexA0412, InterfaceInstWithNamedParams) {
  auto r = Parse("module m; my_if #(.W(16)) u0(.a(a)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "my_if");
  ASSERT_EQ(item->inst_params.size(), 1u);
  EXPECT_EQ(item->inst_params[0].first, "W");
}

// --- interface_instantiation: multiple hierarchical_instance ---
TEST(ParserAnnexA0412, MultipleInterfaceInstances) {
  auto r = Parse("module m; my_if u0(.a(a)), u1(.a(b)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  auto* i0 = r.cu->modules[0]->items[0];
  auto* i1 = r.cu->modules[0]->items[1];
  EXPECT_EQ(i0->inst_module, "my_if");
  EXPECT_EQ(i0->inst_name, "u0");
  EXPECT_EQ(i1->inst_module, "my_if");
  EXPECT_EQ(i1->inst_name, "u1");
}

// --- interface_instantiation: with instance array ---
TEST(ParserAnnexA0412, InterfaceInstArray) {
  auto r = Parse("module m; my_if u0 [3:0] (.a(a)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_module, "my_if");
  EXPECT_NE(item->inst_range_left, nullptr);
  EXPECT_NE(item->inst_range_right, nullptr);
}

// --- interface_instantiation: empty port list ---
TEST(ParserAnnexA0412, InterfaceInstEmptyPorts) {
  auto r = Parse("module m; my_if u0(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_TRUE(item->inst_ports.empty());
}

// --- interface_instantiation: wildcard port ---
TEST(ParserAnnexA0412, InterfaceInstWildcardPort) {
  auto r = Parse("module m; my_if u0(.*); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->inst_wildcard);
}

// --- interface_instantiation: ordered port connections ---
TEST(ParserAnnexA0412, InterfaceInstOrderedPorts) {
  auto r = Parse("module m; my_if u0(a, b, c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_ports.size(), 3u);
}

// --- interface_instantiation: interface instantiated inside interface ---
TEST(ParserAnnexA0412, InterfaceInstInsideInterface) {
  auto r = Parse(
      "interface outer_if;\n"
      "  inner_if u0(.clk(clk));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  ASSERT_GE(r.cu->interfaces[0]->items.size(), 1u);
  auto* item = r.cu->interfaces[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "inner_if");
  EXPECT_EQ(item->inst_name, "u0");
}

// --- interface_instantiation: with empty parameter ---
TEST(ParserAnnexA0412, InterfaceInstEmptyParam) {
  auto r = Parse("module m; my_if #() u0(.a(a)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_module, "my_if");
  EXPECT_TRUE(item->inst_params.empty());
}

// --- interface_instantiation: named port without parentheses ---
TEST(ParserAnnexA0412, InterfaceInstNamedPortNoParens) {
  auto r = Parse("module m; my_if u0(.clk, .rst); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 2u);
  EXPECT_EQ(item->inst_ports[0].first, "clk");
  EXPECT_EQ(item->inst_ports[1].first, "rst");
}

// =============================================================================
// Elaboration tests -- interface instantiation resolved through elaborator
// =============================================================================
// --- Elaborator resolves interface instantiation within a module ---
TEST(ParserAnnexA0412, ElaborationInterfaceInstInModule) {
  ElabFixture f;
  auto* design = Elaborate(
      "interface my_bus(input logic clk, input logic rst);\n"
      "endinterface\n"
      "module top;\n"
      "  logic clk, rst;\n"
      "  my_bus bus0(.clk(clk), .rst(rst));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].module_name, "my_bus");
  EXPECT_EQ(top->children[0].inst_name, "bus0");
  EXPECT_NE(top->children[0].resolved, nullptr);
}

// --- Elaborator resolves interface instantiation with port bindings ---
TEST(ParserAnnexA0412, ElaborationInterfaceInstPortBindings) {
  ElabFixture f;
  auto* design = Elaborate(
      "interface simple_if(input logic data);\n"
      "endinterface\n"
      "module top;\n"
      "  logic d;\n"
      "  simple_if u0(.data(d));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 1u);
  EXPECT_GE(top->children[0].port_bindings.size(), 1u);
  EXPECT_EQ(top->children[0].port_bindings[0].port_name, "data");
}

// --- Elaborator resolves interface inside interface ---
TEST(ParserAnnexA0412, ElaborationInterfaceInsideInterface) {
  ElabFixture f;
  auto* design = Elaborate(
      "interface inner_if(input logic sig);\n"
      "endinterface\n"
      "interface outer_if;\n"
      "  logic sig;\n"
      "  inner_if u0(.sig(sig));\n"
      "endinterface\n"
      "module top;\n"
      "  outer_if oi();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].module_name, "outer_if");
  auto* outer = top->children[0].resolved;
  ASSERT_NE(outer, nullptr);
  ASSERT_GE(outer->children.size(), 1u);
  EXPECT_EQ(outer->children[0].module_name, "inner_if");
  EXPECT_NE(outer->children[0].resolved, nullptr);
}

// =============================================================================
// A.4.1.3 -- Program instantiation
//
// program_instantiation ::=
//   program_identifier [ parameter_value_assignment ]
//     hierarchical_instance { , hierarchical_instance } ;
// =============================================================================
// --- program_instantiation: basic ---
TEST(ParserAnnexA0413, BasicProgramInst) {
  auto r = Parse(
      "program my_prog(input logic clk);\n"
      "endprogram\n"
      "module m; my_prog u0(.clk(clk)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "my_prog");
  EXPECT_EQ(item->inst_name, "u0");
}

// --- program_instantiation: with parameter_value_assignment (ordered) ---
TEST(ParserAnnexA0413, ProgramInstWithOrderedParams) {
  auto r = Parse(
      "program my_prog #(parameter int W = 8)(input logic [W-1:0] data);\n"
      "endprogram\n"
      "module m; my_prog #(16) u0(.data(d)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "my_prog");
  EXPECT_EQ(item->inst_name, "u0");
  ASSERT_EQ(item->inst_params.size(), 1u);
}

// --- program_instantiation: with named parameter_value_assignment ---
TEST(ParserAnnexA0413, ProgramInstWithNamedParams) {
  auto r = Parse(
      "program my_prog #(parameter int W = 8)(input logic [W-1:0] data);\n"
      "endprogram\n"
      "module m; my_prog #(.W(16)) u0(.data(d)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_module, "my_prog");
  ASSERT_EQ(item->inst_params.size(), 1u);
  EXPECT_EQ(item->inst_params[0].first, "W");
}

// --- program_instantiation: multiple hierarchical_instance ---
TEST(ParserAnnexA0413, MultipleProgramInstances) {
  auto r = Parse(
      "program my_prog(input logic clk);\n"
      "endprogram\n"
      "module m; my_prog u0(.clk(a)), u1(.clk(b)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  auto* i0 = r.cu->modules[0]->items[0];
  auto* i1 = r.cu->modules[0]->items[1];
  EXPECT_EQ(i0->inst_module, "my_prog");
  EXPECT_EQ(i0->inst_name, "u0");
  EXPECT_EQ(i1->inst_module, "my_prog");
  EXPECT_EQ(i1->inst_name, "u1");
}

// --- program_instantiation: with instance array ---
TEST(ParserAnnexA0413, ProgramInstArray) {
  auto r = Parse(
      "program my_prog(input logic clk);\n"
      "endprogram\n"
      "module m; my_prog u0 [3:0] (.clk(clk)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_module, "my_prog");
  EXPECT_NE(item->inst_range_left, nullptr);
  EXPECT_NE(item->inst_range_right, nullptr);
}

// --- program_instantiation: empty port list ---
TEST(ParserAnnexA0413, ProgramInstEmptyPorts) {
  auto r = Parse(
      "program my_prog;\n"
      "endprogram\n"
      "module m; my_prog u0(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_TRUE(item->inst_ports.empty());
}

// --- program_instantiation: wildcard port ---
TEST(ParserAnnexA0413, ProgramInstWildcardPort) {
  auto r = Parse(
      "program my_prog(input logic clk);\n"
      "endprogram\n"
      "module m; my_prog u0(.*); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->inst_wildcard);
}

// --- program_instantiation: ordered port connections ---
TEST(ParserAnnexA0413, ProgramInstOrderedPorts) {
  auto r = Parse(
      "program my_prog(input logic a, input logic b, input logic c);\n"
      "endprogram\n"
      "module m; my_prog u0(a, b, c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_ports.size(), 3u);
}

// --- program_instantiation: named port without parentheses ---
TEST(ParserAnnexA0413, ProgramInstNamedPortNoParens) {
  auto r = Parse(
      "program my_prog(input logic clk, input logic rst);\n"
      "endprogram\n"
      "module m; my_prog u0(.clk, .rst); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 2u);
  EXPECT_EQ(item->inst_ports[0].first, "clk");
  EXPECT_EQ(item->inst_ports[1].first, "rst");
}

// --- program_instantiation: empty parameter list ---
TEST(ParserAnnexA0413, ProgramInstEmptyParam) {
  auto r = Parse(
      "program my_prog(input logic clk);\n"
      "endprogram\n"
      "module m; my_prog #() u0(.clk(clk)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_module, "my_prog");
  EXPECT_TRUE(item->inst_params.empty());
}

// =============================================================================
// Elaboration tests -- program instantiation resolved through elaborator
// =============================================================================
// --- Elaborator resolves program instantiation within a module ---
TEST(ParserAnnexA0413, ElaborationProgramInstInModule) {
  ElabFixture f;
  auto* design = Elaborate(
      "program my_prog(input logic clk, input logic rst);\n"
      "endprogram\n"
      "module top;\n"
      "  logic clk, rst;\n"
      "  my_prog p0(.clk(clk), .rst(rst));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].module_name, "my_prog");
  EXPECT_EQ(top->children[0].inst_name, "p0");
  EXPECT_NE(top->children[0].resolved, nullptr);
}

}  // namespace
