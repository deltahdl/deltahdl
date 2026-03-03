// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

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

static ModuleItem* FirstItem(ParseResult6h& r) {
  if (!r.cu || r.cu->modules.empty() || r.cu->modules[0]->items.empty())
    return nullptr;
  return r.cu->modules[0]->items[0];
}

namespace {

// 30b. More integer types as ports: longint and shortint.
TEST(ParserSection6, Sec6_11_LongintShortintAsPorts) {
  auto r = Parse(
      "module m(input longint addr, output shortint result);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 2u);
  EXPECT_EQ(ports[0].data_type.kind, DataTypeKind::kLongint);
  EXPECT_EQ(ports[0].name, "addr");
  EXPECT_EQ(ports[1].data_type.kind, DataTypeKind::kShortint);
  EXPECT_EQ(ports[1].name, "result");
}

// 30c. Integer type port with packed dimensions.
TEST(ParserSection6, Sec6_11_LogicPackedDimsAsPort) {
  auto r = Parse(
      "module m(input logic [7:0] data, output logic [15:0] addr);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 2u);
  EXPECT_EQ(ports[0].data_type.kind, DataTypeKind::kLogic);
  ASSERT_NE(ports[0].data_type.packed_dim_left, nullptr);
  EXPECT_EQ(ports[0].data_type.packed_dim_left->int_val, 7u);
  EXPECT_EQ(ports[1].data_type.kind, DataTypeKind::kLogic);
  ASSERT_NE(ports[1].data_type.packed_dim_left, nullptr);
  EXPECT_EQ(ports[1].data_type.packed_dim_left->int_val, 15u);
}

// =============================================================================
// LRM section 6.11 -- Additional coverage for integer types
// =============================================================================
// Longint with initializer.
TEST(ParserSection6, Sec6_11_LongintWithInit) {
  auto r = Parse(
      "module t;\n"
      "  longint big = 64'hDEAD_BEEF_CAFE_BABE;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLongint);
  ASSERT_NE(item->init_expr, nullptr);
}

// Integer (4-state) with initializer.
TEST(ParserSection6, Sec6_11_IntegerWithInit) {
  auto r = Parse(
      "module t;\n"
      "  integer idx = 0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInteger);
  ASSERT_NE(item->init_expr, nullptr);
}

// Longint function return type.
TEST(ParserSection6, Sec6_11_LongintFunctionReturnType) {
  auto r = Parse(
      "module t;\n"
      "  function longint get_id();\n"
      "    return 64'd1;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kLongint);
}

// Integer function return type.
TEST(ParserSection6, Sec6_11_IntegerFunctionReturnType) {
  auto r = Parse(
      "module t;\n"
      "  function integer get_count();\n"
      "    return 42;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kInteger);
}

// reg unsigned override.
TEST(ParserSection6, Sec6_11_2_RegUnsignedExplicit) {
  auto r = Parse(
      "module t;\n"
      "  reg unsigned [7:0] ru;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReg);
  EXPECT_FALSE(item->data_type.is_signed);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
}

// Multiple integer types as function parameters with directions.
TEST(ParserSection6, Sec6_11_MixedIntegerFuncParams) {
  auto r = Parse(
      "module t;\n"
      "  function void process(input byte cmd, input int data,\n"
      "                        output longint result);\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  ASSERT_EQ(item->func_args.size(), 3u);
  EXPECT_EQ(item->func_args[0].data_type.kind, DataTypeKind::kByte);
  EXPECT_EQ(item->func_args[1].data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(item->func_args[2].data_type.kind, DataTypeKind::kLongint);
  EXPECT_EQ(item->func_args[2].direction, Direction::kOutput);
}

// Integer type with unpacked dimension using range notation.
TEST(ParserSection6, Sec6_11_IntUnpackedRangeNotation) {
  auto r = Parse(
      "module t;\n"
      "  int data [0:7];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_FALSE(item->unpacked_dims.empty());
}

// time type with unpacked dimensions.
TEST(ParserSection6, Sec6_11_TimeUnpackedArray) {
  auto r = Parse(
      "module t;\n"
      "  time timestamps[10];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTime);
  EXPECT_EQ(item->name, "timestamps");
  EXPECT_FALSE(item->unpacked_dims.empty());
}

// integer (4-state) as port declaration.
TEST(ParserSection6, Sec6_11_IntegerAsPort) {
  auto r = Parse(
      "module m(input integer idx);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 1u);
  EXPECT_EQ(ports[0].data_type.kind, DataTypeKind::kInteger);
  EXPECT_EQ(ports[0].direction, Direction::kInput);
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

}  // namespace
