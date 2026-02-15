#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult6h {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult6h Parse(const std::string& src) {
  ParseResult6h result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static bool ParseOk(const std::string& src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

static ModuleItem* FirstItem(ParseResult6h& r) {
  if (!r.cu || r.cu->modules.empty() || r.cu->modules[0]->items.empty())
    return nullptr;
  return r.cu->modules[0]->items[0];
}

// =============================================================================
// LRM section 6.5 -- Nets and variables
// =============================================================================

// 1. Wire net declaration produces kNetDecl with is_net=true.
TEST(ParserSection6, Sec6_5_WireNetDeclKind) {
  auto r = Parse(
      "module t;\n"
      "  wire w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kWire);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_EQ(item->name, "w");
}

// 2. Logic variable declaration produces kVarDecl with is_net=false.
TEST(ParserSection6, Sec6_5_LogicVarDeclKind) {
  auto r = Parse(
      "module t;\n"
      "  logic v;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_FALSE(item->data_type.is_net);
  EXPECT_EQ(item->name, "v");
}

// 3. Reg variable declaration produces kVarDecl.
TEST(ParserSection6, Sec6_5_RegVarDeclKind) {
  auto r = Parse(
      "module t;\n"
      "  reg r;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReg);
  EXPECT_FALSE(item->data_type.is_net);
}

// 4. Int variable declaration.
TEST(ParserSection6, Sec6_5_IntVarDeclKind) {
  auto r = Parse(
      "module t;\n"
      "  int count;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_FALSE(item->data_type.is_net);
  EXPECT_EQ(item->name, "count");
}

// 5. Real variable declaration.
TEST(ParserSection6, Sec6_5_RealVarDeclKind) {
  auto r = Parse(
      "module t;\n"
      "  real voltage;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReal);
  EXPECT_FALSE(item->data_type.is_net);
}

// 6. Wire with packed dimensions [7:0].
TEST(ParserSection6, Sec6_5_WirePackedDims) {
  auto r = Parse(
      "module t;\n"
      "  wire [7:0] bus;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_net);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  ASSERT_NE(item->data_type.packed_dim_right, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 7u);
  EXPECT_EQ(item->data_type.packed_dim_right->int_val, 0u);
}

// 7. Logic with packed dimensions [15:0].
TEST(ParserSection6, Sec6_5_LogicPackedDims) {
  auto r = Parse(
      "module t;\n"
      "  logic [15:0] addr;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_FALSE(item->data_type.is_net);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  ASSERT_NE(item->data_type.packed_dim_right, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 15u);
  EXPECT_EQ(item->data_type.packed_dim_right->int_val, 0u);
}

// 8. Wire with unpacked dimensions [0:3].
TEST(ParserSection6, Sec6_5_WireUnpackedDims) {
  auto r = Parse(
      "module t;\n"
      "  wire w [0:3];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_FALSE(item->unpacked_dims.empty());
}

// 9. Logic with unpacked dimension [4].
TEST(ParserSection6, Sec6_5_LogicUnpackedDim) {
  auto r = Parse(
      "module t;\n"
      "  logic arr [4];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_FALSE(item->data_type.is_net);
  EXPECT_EQ(item->name, "arr");
  EXPECT_FALSE(item->unpacked_dims.empty());
}

// 10. Wire with implicit continuous assignment (wire w = 1).
TEST(ParserSection6, Sec6_5_WireImplicitContAssign) {
  auto r = Parse(
      "module t;\n"
      "  wire w = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_net);
  ASSERT_NE(item->init_expr, nullptr);
}

// 11. Variable with initialization (logic v = 0).
TEST(ParserSection6, Sec6_5_LogicVarInit) {
  auto r = Parse(
      "module t;\n"
      "  logic v = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_FALSE(item->data_type.is_net);
  ASSERT_NE(item->init_expr, nullptr);
}

// 12. Net driven by assign statement produces kContAssign.
TEST(ParserSection6, Sec6_5_NetDrivenByContAssign) {
  auto r = Parse(
      "module t;\n"
      "  wire out;\n"
      "  assign out = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 2u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kContAssign);
  ASSERT_NE(items[1]->assign_lhs, nullptr);
  ASSERT_NE(items[1]->assign_rhs, nullptr);
}

// 13. Variable driven by initial block (procedural assignment).
TEST(ParserSection6, Sec6_5_VarDrivenByInitialBlock) {
  auto r = Parse(
      "module t;\n"
      "  logic q;\n"
      "  initial q = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 2u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kInitialBlock);
  ASSERT_NE(items[1]->body, nullptr);
}

// 14. Variable driven by always_comb.
TEST(ParserSection6, Sec6_5_VarDrivenByAlwaysComb) {
  auto r = Parse(
      "module t;\n"
      "  logic a, y;\n"
      "  always_comb y = a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  bool found_comb = false;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kAlwaysCombBlock) {
      found_comb = true;
      ASSERT_NE(item->body, nullptr);
    }
  }
  EXPECT_TRUE(found_comb);
}

// 15. Variable driven by always_ff with clock sensitivity.
TEST(ParserSection6, Sec6_5_VarDrivenByAlwaysFF) {
  auto r = Parse(
      "module t;\n"
      "  logic clk, q, d;\n"
      "  always_ff @(posedge clk) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  bool found_ff = false;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kAlwaysFFBlock) {
      found_ff = true;
      ASSERT_NE(item->body, nullptr);
    }
  }
  EXPECT_TRUE(found_ff);
}

// 16. Variable with continuous assignment (assign logic_var = expr).
TEST(ParserSection6, Sec6_5_VarWithContAssign) {
  auto r = Parse(
      "module t;\n"
      "  logic y;\n"
      "  assign y = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 2u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(items[0]->data_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kContAssign);
}

// 17. Multiple wire declarations on one line.
TEST(ParserSection6, Sec6_5_MultipleWireDecls) {
  auto r = Parse(
      "module t;\n"
      "  wire a, b, c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 3u);
  for (auto* item : items) {
    EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
    EXPECT_TRUE(item->data_type.is_net);
  }
  EXPECT_EQ(items[0]->name, "a");
  EXPECT_EQ(items[1]->name, "b");
  EXPECT_EQ(items[2]->name, "c");
}

// 18. Multiple logic declarations on one line.
TEST(ParserSection6, Sec6_5_MultipleLogicDecls) {
  auto r = Parse(
      "module t;\n"
      "  logic x, y, z;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 3u);
  for (auto* item : items) {
    EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
    EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
    EXPECT_FALSE(item->data_type.is_net);
  }
  EXPECT_EQ(items[0]->name, "x");
  EXPECT_EQ(items[1]->name, "y");
  EXPECT_EQ(items[2]->name, "z");
}

// 19. Tri net type declaration.
TEST(ParserSection6, Sec6_5_TriNetDecl) {
  auto r = Parse(
      "module t;\n"
      "  tri [3:0] bus;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTri);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_EQ(item->name, "bus");
}

// 20. Supply0 and supply1 net declarations.
TEST(ParserSection6, Sec6_5_Supply0AndSupply1) {
  auto r = Parse(
      "module t;\n"
      "  supply0 gnd;\n"
      "  supply1 vdd;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 2u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(items[0]->data_type.kind, DataTypeKind::kSupply0);
  EXPECT_TRUE(items[0]->data_type.is_net);
  EXPECT_EQ(items[0]->name, "gnd");
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(items[1]->data_type.kind, DataTypeKind::kSupply1);
  EXPECT_TRUE(items[1]->data_type.is_net);
  EXPECT_EQ(items[1]->name, "vdd");
}

// 21. Trireg net declaration.
TEST(ParserSection6, Sec6_5_TriregDecl) {
  auto r = Parse(
      "module t;\n"
      "  trireg cap;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTrireg);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_EQ(item->name, "cap");
}

// 22. Uwire net declaration.
TEST(ParserSection6, Sec6_5_UwireDecl) {
  auto r = Parse(
      "module t;\n"
      "  uwire single;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kUwire);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_EQ(item->name, "single");
}

// 23. String variable declaration.
TEST(ParserSection6, Sec6_5_StringVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  string msg;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kString);
  EXPECT_FALSE(item->data_type.is_net);
  EXPECT_EQ(item->name, "msg");
}

// 24. Event variable declaration.
TEST(ParserSection6, Sec6_5_EventVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  event done;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kEvent);
  EXPECT_FALSE(item->data_type.is_net);
  EXPECT_EQ(item->name, "done");
}

// 25. Chandle variable declaration.
TEST(ParserSection6, Sec6_5_ChandleVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  chandle handle;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kChandle);
  EXPECT_FALSE(item->data_type.is_net);
  EXPECT_EQ(item->name, "handle");
}

// 26. Mixed net and variable declarations coexist in same module.
TEST(ParserSection6, Sec6_5_MixedNetAndVarDecls) {
  auto r = Parse(
      "module t;\n"
      "  wire [7:0] net_a;\n"
      "  logic [7:0] var_b;\n"
      "  tri net_c;\n"
      "  int var_d;\n"
      "  reg var_e;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 5u);
  // Nets
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(items[0]->data_type.is_net);
  EXPECT_EQ(items[2]->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(items[2]->data_type.is_net);
  // Variables
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kVarDecl);
  EXPECT_FALSE(items[1]->data_type.is_net);
  EXPECT_EQ(items[3]->kind, ModuleItemKind::kVarDecl);
  EXPECT_FALSE(items[3]->data_type.is_net);
  EXPECT_EQ(items[4]->kind, ModuleItemKind::kVarDecl);
  EXPECT_FALSE(items[4]->data_type.is_net);
}

// 27. Net as input port.
TEST(ParserSection6, Sec6_5_NetAsInputPort) {
  auto r = Parse(
      "module t(input wire [7:0] data_in);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 1u);
  EXPECT_EQ(ports[0].direction, Direction::kInput);
  EXPECT_EQ(ports[0].data_type.kind, DataTypeKind::kWire);
  EXPECT_TRUE(ports[0].data_type.is_net);
  EXPECT_EQ(ports[0].name, "data_in");
  ASSERT_NE(ports[0].data_type.packed_dim_left, nullptr);
  EXPECT_EQ(ports[0].data_type.packed_dim_left->int_val, 7u);
}

// 28. Variable as output port.
TEST(ParserSection6, Sec6_5_VarAsOutputPort) {
  auto r = Parse(
      "module t(output logic [15:0] result);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 1u);
  EXPECT_EQ(ports[0].direction, Direction::kOutput);
  EXPECT_EQ(ports[0].data_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(ports[0].name, "result");
  ASSERT_NE(ports[0].data_type.packed_dim_left, nullptr);
  EXPECT_EQ(ports[0].data_type.packed_dim_left->int_val, 15u);
}

// 29. Net and variable with same-width packed vectors.
TEST(ParserSection6, Sec6_5_NetAndVarSameWidthVectors) {
  auto r = Parse(
      "module t;\n"
      "  wire [31:0] net_data;\n"
      "  logic [31:0] var_data;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 2u);
  // Wire net
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(items[0]->data_type.is_net);
  ASSERT_NE(items[0]->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(items[0]->data_type.packed_dim_left->int_val, 31u);
  // Logic variable
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kVarDecl);
  EXPECT_FALSE(items[1]->data_type.is_net);
  ASSERT_NE(items[1]->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(items[1]->data_type.packed_dim_left->int_val, 31u);
}

// 30. Reg used in always block (procedural context).
TEST(ParserSection6, Sec6_5_RegInAlwaysBlock) {
  auto r = Parse(
      "module t;\n"
      "  reg clk;\n"
      "  always #5 clk = ~clk;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 2u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(items[0]->data_type.kind, DataTypeKind::kReg);
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kAlwaysBlock);
  ASSERT_NE(items[1]->body, nullptr);
}
