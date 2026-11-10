#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

const ModuleDecl* OnlyModule(const ParseResult& r) {
  if (r.cu == nullptr || r.has_errors || r.cu->modules.size() != 1) {
    return nullptr;
  }
  return r.cu->modules[0];
}

TEST(ModuleBuildingBlock, ModuleEndmoduleEnclosesTheBlock) {
  auto r = Parse(
      "module mux2to1;\n"
      "endmodule : mux2to1\n");
  const auto* m = OnlyModule(r);
  ASSERT_NE(m, nullptr);
  EXPECT_EQ(m->name, "mux2to1");
  EXPECT_EQ(m->decl_kind, ModuleDeclKind::kModule);
}

TEST(ModuleBuildingBlock, HoldsPortsDeclaredInItsHeader) {
  auto r = Parse(
      "module m(input wire a, output logic y);\n"
      "endmodule\n");
  const auto* m = OnlyModule(r);
  ASSERT_NE(m, nullptr);
  ASSERT_EQ(m->ports.size(), 2u);
  EXPECT_EQ(m->ports[0].name, "a");
  EXPECT_EQ(m->ports[0].direction, Direction::kInput);
  EXPECT_EQ(m->ports[1].name, "y");
  EXPECT_EQ(m->ports[1].direction, Direction::kOutput);
}

TEST(ModuleBuildingBlock, HoldsPortsDeclaredInItsBody) {
  auto r = Parse(
      "module m(a, y);\n"
      "  input a;\n"
      "  output y;\n"
      "endmodule\n");
  const auto* m = OnlyModule(r);
  ASSERT_NE(m, nullptr);
  ASSERT_EQ(m->ports.size(), 2u);
  EXPECT_EQ(m->ports[0].name, "a");
  EXPECT_EQ(m->ports[0].direction, Direction::kInput);
  EXPECT_EQ(m->ports[1].name, "y");
  EXPECT_EQ(m->ports[1].direction, Direction::kOutput);
}

TEST(ModuleBuildingBlock, HoldsANetDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  wire [3:0] bus;\n"
      "endmodule\n");
  const auto* m = OnlyModule(r);
  ASSERT_NE(m, nullptr);
  const auto* item = FindItemByKind(m->items, ModuleItemKind::kNetDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "bus");
}

TEST(ModuleBuildingBlock, HoldsAVariableDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] count;\n"
      "endmodule\n");
  const auto* m = OnlyModule(r);
  ASSERT_NE(m, nullptr);
  const auto* item = FindItemByKind(m->items, ModuleItemKind::kVarDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "count");
}

TEST(ModuleBuildingBlock, HoldsAStructureVariable) {
  auto r = Parse(
      "module m;\n"
      "  struct packed { logic [3:0] hi; logic [3:0] lo; } pair;\n"
      "endmodule\n");
  const auto* m = OnlyModule(r);
  ASSERT_NE(m, nullptr);
  const auto* item = FindItemByKind(m->items, ModuleItemKind::kVarDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "pair");
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kStruct);
  EXPECT_EQ(item->data_type.struct_members.size(), 2u);
}

TEST(ModuleBuildingBlock, HoldsAUnionVariable) {
  auto r = Parse(
      "module m;\n"
      "  union packed { logic [7:0] whole; logic [7:0] bits; } view;\n"
      "endmodule\n");
  const auto* m = OnlyModule(r);
  ASSERT_NE(m, nullptr);
  const auto* item = FindItemByKind(m->items, ModuleItemKind::kVarDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "view");
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kUnion);
}

TEST(ModuleBuildingBlock, HoldsAParameterConstant) {
  auto r = Parse(
      "module m;\n"
      "  parameter int WIDTH = 8;\n"
      "endmodule\n");
  const auto* m = OnlyModule(r);
  ASSERT_NE(m, nullptr);
  const auto* item = FindItemByKind(m->items, ModuleItemKind::kParamDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "WIDTH");
  EXPECT_FALSE(item->is_localparam);
}

TEST(ModuleBuildingBlock, HoldsALocalparamConstant) {
  auto r = Parse(
      "module m;\n"
      "  localparam int DEPTH = 16;\n"
      "endmodule\n");
  const auto* m = OnlyModule(r);
  ASSERT_NE(m, nullptr);
  const auto* item = FindItemByKind(m->items, ModuleItemKind::kParamDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "DEPTH");
  EXPECT_TRUE(item->is_localparam);
}

TEST(ModuleBuildingBlock, HoldsAConstVariable) {
  auto r = Parse(
      "module m;\n"
      "  const int limit = 3;\n"
      "endmodule\n");
  const auto* m = OnlyModule(r);
  ASSERT_NE(m, nullptr);
  const auto* item = FindItemByKind(m->items, ModuleItemKind::kVarDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "limit");
  EXPECT_TRUE(item->data_type.is_const);
}

TEST(ModuleBuildingBlock, HoldsAUserDefinedType) {
  auto r = Parse(
      "module m;\n"
      "  typedef logic [3:0] nibble_t;\n"
      "endmodule\n");
  const auto* m = OnlyModule(r);
  ASSERT_NE(m, nullptr);
  const auto* item = FindItemByKind(m->items, ModuleItemKind::kTypedef);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "nibble_t");
}

TEST(ModuleBuildingBlock, HoldsAClassDefinition) {
  auto r = Parse(
      "module m;\n"
      "  class Packet;\n"
      "    int id;\n"
      "  endclass\n"
      "endmodule\n");
  const auto* m = OnlyModule(r);
  ASSERT_NE(m, nullptr);
  const auto* item = FindItemByKind(m->items, ModuleItemKind::kClassDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "Packet");
}

TEST(ModuleBuildingBlock, HoldsAnImportFromAPackage) {
  auto r = Parse(
      "package pk;\n"
      "  int shared;\n"
      "endpackage\n"
      "module m;\n"
      "  import pk::shared;\n"
      "endmodule\n");
  const auto* m = OnlyModule(r);
  ASSERT_NE(m, nullptr);
  const auto* item = FindItemByKind(m->items, ModuleItemKind::kImportDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->import_item.package_name, "pk");
  EXPECT_EQ(item->import_item.item_name, "shared");
}

TEST(ModuleBuildingBlock, HoldsAFunctionDefinition) {
  auto r = Parse(
      "module m;\n"
      "  function int twice(int x);\n"
      "    return 2 * x;\n"
      "  endfunction\n"
      "endmodule\n");
  const auto* m = OnlyModule(r);
  ASSERT_NE(m, nullptr);
  const auto* item = FindItemByKind(m->items, ModuleItemKind::kFunctionDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "twice");
}

TEST(ModuleBuildingBlock, HoldsATaskDefinition) {
  auto r = Parse(
      "module m;\n"
      "  task pause(input int cycles);\n"
      "  endtask\n"
      "endmodule\n");
  const auto* m = OnlyModule(r);
  ASSERT_NE(m, nullptr);
  const auto* item = FindItemByKind(m->items, ModuleItemKind::kTaskDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "pause");
}

TEST(ModuleBuildingBlock, HoldsAnInstanceOfAnotherModule) {
  auto r = Parse(
      "module leaf;\n"
      "endmodule\n"
      "module top;\n"
      "  leaf u_leaf();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 2u);
  const auto* item =
      FindItemByKind(r.cu->modules[1]->items, ModuleItemKind::kModuleInst);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->inst_module, "leaf");
  EXPECT_EQ(item->inst_name, "u_leaf");
}

TEST(ModuleBuildingBlock, HoldsAProgramInstance) {
  auto r = Parse(
      "program bench;\n"
      "endprogram\n"
      "module m;\n"
      "  bench u_bench();\n"
      "endmodule\n");
  const auto* m = OnlyModule(r);
  ASSERT_NE(m, nullptr);
  const auto* item = FindItemByKind(m->items, ModuleItemKind::kModuleInst);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->inst_module, "bench");
  EXPECT_EQ(item->inst_name, "u_bench");
}

TEST(ModuleBuildingBlock, HoldsAnInterfaceInstance) {
  auto r = Parse(
      "interface bus_if;\n"
      "endinterface\n"
      "module m;\n"
      "  bus_if u_bus();\n"
      "endmodule\n");
  const auto* m = OnlyModule(r);
  ASSERT_NE(m, nullptr);
  const auto* item = FindItemByKind(m->items, ModuleItemKind::kModuleInst);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->inst_module, "bus_if");
  EXPECT_EQ(item->inst_name, "u_bus");
}

TEST(ModuleBuildingBlock, HoldsACheckerInstance) {
  auto r = Parse(
      "checker never_high(logic sig);\n"
      "endchecker\n"
      "module m;\n"
      "  logic s;\n"
      "  never_high u_check(s);\n"
      "endmodule\n");
  const auto* m = OnlyModule(r);
  ASSERT_NE(m, nullptr);
  const auto* item = FindItemByKind(m->items, ModuleItemKind::kModuleInst);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->inst_module, "never_high");
  EXPECT_EQ(item->inst_name, "u_check");
}

TEST(ModuleBuildingBlock, HoldsAGatePrimitiveInstance) {
  auto r = Parse(
      "module m(input a, input b, output y);\n"
      "  and g1(y, a, b);\n"
      "endmodule\n");
  const auto* m = OnlyModule(r);
  ASSERT_NE(m, nullptr);
  const auto* item = FindItemByKind(m->items, ModuleItemKind::kGateInst);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->gate_kind, GateKind::kAnd);
  EXPECT_EQ(item->gate_inst_name, "g1");
}

TEST(ModuleBuildingBlock, HoldsAUserDefinedPrimitiveInstance) {
  auto r = Parse(
      "primitive buf_udp(output o, input i);\n"
      "  table\n"
      "    0 : 0;\n"
      "    1 : 1;\n"
      "  endtable\n"
      "endprimitive\n"
      "module m(input a, output y);\n"
      "  buf_udp u1(y, a);\n"
      "endmodule\n");
  const auto* m = OnlyModule(r);
  ASSERT_NE(m, nullptr);
  const auto* item = FindItemByKind(m->items, ModuleItemKind::kUdpInst);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->inst_module, "buf_udp");
  EXPECT_EQ(item->gate_inst_name, "u1");
  EXPECT_EQ(item->gate_terminals.size(), 2u);
}

TEST(ModuleBuildingBlock, HoldsAClassObjectInstance) {
  auto r = Parse(
      "module m;\n"
      "  class Packet;\n"
      "  endclass\n"
      "  Packet pkt = new;\n"
      "endmodule\n");
  const auto* m = OnlyModule(r);
  ASSERT_NE(m, nullptr);
  const auto* item = FindItemByKind(m->items, ModuleItemKind::kVarDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "pkt");
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(item->data_type.type_name, "Packet");
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(ModuleBuildingBlock, HoldsAContinuousAssignment) {
  auto r = Parse(
      "module m(input a, output y);\n"
      "  assign y = ~a;\n"
      "endmodule\n");
  const auto* m = OnlyModule(r);
  ASSERT_NE(m, nullptr);
  const auto* item = FindItemByKind(m->items, ModuleItemKind::kContAssign);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->assign_lhs, nullptr);
  EXPECT_NE(item->assign_rhs, nullptr);
}

TEST(ModuleBuildingBlock, HoldsEveryKindOfProceduralBlock) {
  auto r = Parse(
      "module m(input clk, input d, output logic q, output logic c,\n"
      "         output logic l);\n"
      "  initial q = 0;\n"
      "  final $display(q);\n"
      "  always @(posedge clk) q <= d;\n"
      "  always_comb c = d;\n"
      "  always_ff @(posedge clk) q <= d;\n"
      "  always_latch if (clk) l = d;\n"
      "endmodule\n");
  const auto* m = OnlyModule(r);
  ASSERT_NE(m, nullptr);
  EXPECT_TRUE(HasItemOfKind(m->items, ModuleItemKind::kInitialBlock));
  EXPECT_TRUE(HasItemOfKind(m->items, ModuleItemKind::kFinalBlock));
  EXPECT_TRUE(HasItemOfKind(m->items, ModuleItemKind::kAlwaysBlock));
  EXPECT_TRUE(HasItemOfKind(m->items, ModuleItemKind::kAlwaysCombBlock));
  EXPECT_TRUE(HasItemOfKind(m->items, ModuleItemKind::kAlwaysFFBlock));
  EXPECT_TRUE(HasItemOfKind(m->items, ModuleItemKind::kAlwaysLatchBlock));
}

TEST(ModuleBuildingBlock, HoldsEveryKindOfGenerateBlock) {
  auto r = Parse(
      "module m;\n"
      "  parameter int N = 2;\n"
      "  genvar i;\n"
      "  for (i = 0; i < N; i++) begin : loop\n"
      "    wire w;\n"
      "  end\n"
      "  if (N > 1) begin : cond\n"
      "    wire c;\n"
      "  end\n"
      "  case (N)\n"
      "    2: begin : sel\n"
      "      wire s;\n"
      "    end\n"
      "    default: begin : other\n"
      "      wire o;\n"
      "    end\n"
      "  endcase\n"
      "endmodule\n");
  const auto* m = OnlyModule(r);
  ASSERT_NE(m, nullptr);
  EXPECT_TRUE(HasItemOfKind(m->items, ModuleItemKind::kGenerateFor));
  EXPECT_TRUE(HasItemOfKind(m->items, ModuleItemKind::kGenerateIf));
  EXPECT_TRUE(HasItemOfKind(m->items, ModuleItemKind::kGenerateCase));
}

TEST(ModuleBuildingBlock, HoldsASpecifyBlock) {
  auto r = Parse(
      "module m(input a, output y);\n"
      "  assign y = a;\n"
      "  specify\n"
      "    (a => y) = 2;\n"
      "  endspecify\n"
      "endmodule\n");
  const auto* m = OnlyModule(r);
  ASSERT_NE(m, nullptr);
  EXPECT_TRUE(HasItemOfKind(m->items, ModuleItemKind::kSpecifyBlock));
}

}  // namespace
