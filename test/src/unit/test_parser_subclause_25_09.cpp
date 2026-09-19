#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

TEST(InterfaceParsing, VirtualInterfaceDecl) {
  auto r = Parse(
      "module top;\n"
      "  virtual interface simple_bus bus_if;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kVirtualInterface);
  EXPECT_EQ(item->data_type.type_name, "simple_bus");
  EXPECT_EQ(item->name, "bus_if");
}

TEST(InterfaceParsing, VirtualInterfaceNoKeyword) {
  auto r = Parse(
      "module top;\n"
      "  virtual simple_bus bus_if;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kVirtualInterface);
  EXPECT_EQ(item->data_type.type_name, "simple_bus");
  EXPECT_EQ(item->name, "bus_if");
}

TEST(InterfaceParsing, VirtualInterfaceWithModportNames) {
  auto r = Parse(
      "module top;\n"
      "  virtual interface simple_bus.target bus_if;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.type_name, "simple_bus");
  EXPECT_EQ(item->data_type.modport_name, "target");
}

// Syntax 25-3 admits an optional parameter_value_assignment after the
// interface_identifier. The parser must capture the #(...) override list on the
// virtual-interface data_type, not just the bare type name.
TEST(InterfaceParsing, VirtualInterfaceWithParamValueAssignment) {
  auto r = Parse(
      "module top;\n"
      "  virtual pbus #(16) vif;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kVirtualInterface);
  EXPECT_EQ(item->data_type.type_name, "pbus");
  ASSERT_EQ(item->data_type.type_params.size(), 1u);
  EXPECT_EQ(item->name, "vif");
}

// The optional parameter_value_assignment and the optional . modport_identifier
// may both appear, in that order, on a single virtual-interface declaration
// (e.g. the "virtual PBus #(16).phy v16_phy;" form shown in 25.9). The parser
// must record both the override list and the selected modport.
TEST(InterfaceParsing, VirtualInterfaceWithParamsAndModport) {
  auto r = Parse(
      "module top;\n"
      "  virtual PBus #(16).phy v16_phy;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kVirtualInterface);
  EXPECT_EQ(item->data_type.type_name, "PBus");
  ASSERT_EQ(item->data_type.type_params.size(), 1u);
  EXPECT_EQ(item->data_type.modport_name, "phy");
  EXPECT_EQ(item->name, "v16_phy");
}

TEST(InterfaceParsing, VirtualInterfaceAssignment) {
  auto r = Parse(
      "module top;\n"
      "  virtual interface simple_bus vif;\n"
      "  initial begin\n"
      "    vif = null;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 2);
  EXPECT_EQ(mod->items[0]->data_type.kind, DataTypeKind::kVirtualInterface);
}

TEST(InterfaceParsing, VirtualInterfaceMultipleDecls) {
  auto r = Parse(
      "module top;\n"
      "  virtual interface bus_if a_if;\n"
      "  virtual bus_if b_if;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 2);
  EXPECT_EQ(mod->items[0]->data_type.kind, DataTypeKind::kVirtualInterface);
  EXPECT_EQ(mod->items[0]->name, "a_if");
  EXPECT_EQ(mod->items[1]->data_type.kind, DataTypeKind::kVirtualInterface);
  EXPECT_EQ(mod->items[1]->name, "b_if");
}

TEST(InterfaceParsing, VirtualInterfaceAsTaskArgument) {
  auto r = Parse(
      "interface simple_bus; endinterface\n"
      "module m;\n"
      "  task do_it(virtual simple_bus v); endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(InterfaceParsing, VirtualInterfaceAsFunctionArgument) {
  auto r = Parse(
      "interface simple_bus; endinterface\n"
      "module m;\n"
      "  function int do_it(virtual simple_bus v); return 0; endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(InterfaceParsing, VirtualInterfaceAsMethodArgument) {
  auto r = Parse(
      "interface simple_bus; endinterface\n"
      "class C;\n"
      "  task do_it(virtual simple_bus v); endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(InterfaceParsing, VirtualInterfaceAsClassProperty) {
  auto r = Parse(
      "interface simple_bus; endinterface\n"
      "class C;\n"
      "  virtual simple_bus bus;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(InterfaceParsing, VirtualInterfaceClassPropertyInitFromNewArg) {
  auto r = Parse(
      "interface simple_bus; endinterface\n"
      "class C;\n"
      "  virtual simple_bus bus;\n"
      "  function new(virtual simple_bus b); bus = b; endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(InterfaceParsing, VirtualInterfaceEqualityExpression) {
  auto r = Parse(
      "interface simple_bus; endinterface\n"
      "module m;\n"
      "  virtual simple_bus a, b;\n"
      "  initial if (a == b) $display(\"eq\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(InterfaceParsing, VirtualInterfaceInequalityExpression) {
  auto r = Parse(
      "interface simple_bus; endinterface\n"
      "module m;\n"
      "  virtual simple_bus a;\n"
      "  initial if (a != null) $display(\"init\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §25.9 lets a virtual interface be declared wherever a variable is, and
// A.2.2.1 (printed page 1182) lists `virtual [interface] interface_identifier`
// among data_type's alternatives, so a block item opening with `virtual` is a
// data_declaration wherever A.2.8 places one: the locals of a task or function
// body and the head of a seq_block. IsBlockVarDeclStartCore did not take the
// keyword as opening a declaration, so the parser read the line as a statement
// and reported it.
TEST(InterfaceParsing, VirtualInterfaceFirstLocalOfTask) {
  auto r = Parse(
      "module m;\n"
      "  task t();\n"
      "    virtual simple_bus v;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* t = FindItemByName(r.cu->modules[0]->items, "t");
  ASSERT_NE(t, nullptr);
  ASSERT_GE(t->func_body_stmts.size(), 1u);
  EXPECT_EQ(t->func_body_stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(t->func_body_stmts[0]->var_decl_type.kind,
            DataTypeKind::kVirtualInterface);
  EXPECT_EQ(t->func_body_stmts[0]->var_decl_type.type_name, "simple_bus");
  EXPECT_EQ(t->func_body_stmts[0]->var_name, "v");
}

TEST(InterfaceParsing, VirtualInterfaceWithKeywordFirstLocalOfFunction) {
  auto r = Parse(
      "module m;\n"
      "  function void f();\n"
      "    virtual interface simple_bus v;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* f = FindItemByName(r.cu->modules[0]->items, "f");
  ASSERT_NE(f, nullptr);
  ASSERT_GE(f->func_body_stmts.size(), 1u);
  EXPECT_EQ(f->func_body_stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(f->func_body_stmts[0]->var_decl_type.kind,
            DataTypeKind::kVirtualInterface);
  EXPECT_EQ(f->func_body_stmts[0]->var_name, "v");
}

TEST(InterfaceParsing, VirtualInterfaceFirstItemOfSeqBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    virtual simple_bus v;\n"
      "    v = null;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->kind, StmtKind::kBlock);
  ASSERT_EQ(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(body->stmts[0]->var_decl_type.kind,
            DataTypeKind::kVirtualInterface);
  EXPECT_EQ(body->stmts[0]->var_name, "v");
}

}  // namespace
