// Non-LRM tests

#include "fixture_parser.h"
#include "elaborator/type_eval.h"
#include "helpers_parser_verify.h"

using namespace delta;

struct ParseResult6f {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult6f Parse(const std::string& src) {
  ParseResult6f result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static ModuleItem* FirstItem(ParseResult6f& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

namespace {

// =========================================================================
// §6.22: Cast compatibility
// =========================================================================
TEST(ParserSection6, CastCompatibleRealToIntType) {
  // §6.22.4: real and int are cast compatible.
  DataType a;
  a.kind = DataTypeKind::kReal;
  DataType b;
  b.kind = DataTypeKind::kInt;
  EXPECT_TRUE(IsCastCompatible(a, b));
}

TEST(ParserSection6, CastCompatibleEnumToInt) {
  // §6.22.4: enum and int are cast compatible.
  DataType a;
  a.kind = DataTypeKind::kEnum;
  DataType b;
  b.kind = DataTypeKind::kInt;
  EXPECT_TRUE(IsCastCompatible(a, b));
}

// §6.6.7: Nettype used with resolution function and net declaration.
TEST(ParserSection6, Sec6_6_7_NettypeWithResolveAndNetDecl) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct { real field1; bit field2; } T;\n"
              "  nettype T wTsum with Tsum;\n"
              "  wTsum bus;\n"
              "endmodule\n"));
}

// §6.7.1: Wand net declaration.
TEST(ParserSection6, Sec6_7_1_WandDecl) {
  auto r = Parse(
      "module t;\n"
      "  wand w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kWand);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_EQ(item->name, "w");
}

// §6.7.1: Wor net declaration.
TEST(ParserSection6, Sec6_7_1_WorDecl) {
  auto r = Parse(
      "module t;\n"
      "  wor w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kWor);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_EQ(item->name, "w");
}

// §6.7.1: Triand net declaration.
TEST(ParserSection6, Sec6_7_1_TriandDecl) {
  auto r = Parse(
      "module t;\n"
      "  triand ta;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTriand);
  EXPECT_TRUE(item->data_type.is_net);
}

// §6.7.1: Trior net declaration.
TEST(ParserSection6, Sec6_7_1_TriorDecl) {
  auto r = Parse(
      "module t;\n"
      "  trior to1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTrior);
  EXPECT_TRUE(item->data_type.is_net);
}

// §6.7.1: Tri0 net declaration.
TEST(ParserSection6, Sec6_7_1_Tri0Decl) {
  auto r = Parse(
      "module t;\n"
      "  tri0 t0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTri0);
  EXPECT_TRUE(item->data_type.is_net);
}

// §6.7.1: Tri1 net declaration.
TEST(ParserSection6, Sec6_7_1_Tri1Decl) {
  auto r = Parse(
      "module t;\n"
      "  tri1 t1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTri1);
  EXPECT_TRUE(item->data_type.is_net);
}

// §6.7.1: Supply0 net declaration.
TEST(ParserSection6, Sec6_7_1_Supply0Decl) {
  auto r = Parse(
      "module t;\n"
      "  supply0 gnd;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kSupply0);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_EQ(item->name, "gnd");
}

// §6.7.1: Supply1 net declaration.
TEST(ParserSection6, Sec6_7_1_Supply1Decl) {
  auto r = Parse(
      "module t;\n"
      "  supply1 vdd;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kSupply1);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_EQ(item->name, "vdd");
}

// §6.7.1: Uwire net declaration.
TEST(ParserSection6, Sec6_7_1_UwireDecl) {
  auto r = Parse(
      "module t;\n"
      "  uwire uw;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kUwire);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_EQ(item->name, "uw");
}

// §6.7.1: Net with signed qualifier.
TEST(ParserSection6, Sec6_7_1_WireSignedQualifier) {
  auto r = Parse(
      "module t;\n"
      "  wire signed [7:0] s;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_signed);
  EXPECT_TRUE(item->data_type.is_net);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 7u);
}

// §6.7.1: Net with vectored qualifier.
TEST(ParserSection6, Sec6_7_1_WireVectoredQualifier) {
  auto r = Parse(
      "module t;\n"
      "  wire vectored [7:0] v;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_vectored);
  EXPECT_EQ(item->name, "v");
}

// §6.7.1: Net with scalared qualifier.
TEST(ParserSection6, Sec6_7_1_WireScalaredQualifier) {
  auto r = Parse(
      "module t;\n"
      "  wire scalared [7:0] sc;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_scalared);
  EXPECT_EQ(item->name, "sc");
}

// §6.7.1: Wire with explicit bit type.
TEST(ParserSection6, Sec6_7_1_WireWithBitType) {
  auto r = Parse(
      "module t;\n"
      "  wire bit [3:0] b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_EQ(item->name, "b");
}

// §6.7.1: Net with single delay value.
TEST(ParserSection6, Sec6_7_1_WireWithDelay) {
  auto r = Parse(
      "module t;\n"
      "  wire #5 w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->int_val, 5u);
  EXPECT_EQ(item->net_delay_fall, nullptr);
  EXPECT_EQ(item->net_delay_decay, nullptr);
}

// §6.7.1: Net with two delays (rise, fall).
TEST(ParserSection6, Sec6_7_1_WireTwoDelays) {
  auto r = Parse(
      "module t;\n"
      "  wire #(3, 5) w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->int_val, 3u);
  ASSERT_NE(item->net_delay_fall, nullptr);
  EXPECT_EQ(item->net_delay_fall->int_val, 5u);
  EXPECT_EQ(item->net_delay_decay, nullptr);
}

// §6.7.1: Net with three delays (rise, fall, turnoff).
TEST(ParserSection6, Sec6_7_1_WireThreeDelays) {
  auto r = Parse(
      "module t;\n"
      "  wire #(2, 4, 6) w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->int_val, 2u);
  ASSERT_NE(item->net_delay_fall, nullptr);
  EXPECT_EQ(item->net_delay_fall->int_val, 4u);
  ASSERT_NE(item->net_delay_decay, nullptr);
  EXPECT_EQ(item->net_delay_decay->int_val, 6u);
}

// §6.7.1: Multiple net declarations of different types in the same module.
TEST(ParserSection6, Sec6_7_1_MixedNetTypesInModule) {
  auto r = Parse(
      "module t;\n"
      "  wire w;\n"
      "  tri t1;\n"
      "  wand wa;\n"
      "  supply0 gnd;\n"
      "  supply1 vdd;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 5u);
  EXPECT_EQ(items[0]->data_type.kind, DataTypeKind::kWire);
  EXPECT_EQ(items[1]->data_type.kind, DataTypeKind::kTri);
  EXPECT_EQ(items[2]->data_type.kind, DataTypeKind::kWand);
  EXPECT_EQ(items[3]->data_type.kind, DataTypeKind::kSupply0);
  EXPECT_EQ(items[4]->data_type.kind, DataTypeKind::kSupply1);
}

// §6.7.1: Net declaration with unpacked dimension.
TEST(ParserSection6, Sec6_7_1_WireUnpackedDim) {
  auto r = Parse(
      "module t;\n"
      "  wire w [0:3];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->name, "w");
  EXPECT_FALSE(item->unpacked_dims.empty());
}

// §6.7.1: Wire with both packed and unpacked dimensions.
TEST(ParserSection6, Sec6_7_1_WirePackedAndUnpackedDims) {
  auto r = Parse(
      "module t;\n"
      "  wire [7:0] mem [0:255];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 7u);
  EXPECT_FALSE(item->unpacked_dims.empty());
}

// §6.7.1: Net with drive strength (strong0, pull1).
TEST(ParserSection6, Sec6_7_1_WireDriveStrength) {
  auto r = Parse(
      "module t;\n"
      "  wire (strong0, pull1) w = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  // 4=strong, 3=pull (parser encoding)
  EXPECT_EQ(item->drive_strength0, 4u);
  EXPECT_EQ(item->drive_strength1, 3u);
}

// §6.7.1: Trireg with charge strength (medium).
TEST(ParserSection6, Sec6_7_1_TriregChargeStrengthMedium) {
  auto r = Parse(
      "module t;\n"
      "  trireg (medium) m1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTrireg);
  EXPECT_EQ(item->data_type.charge_strength, 2);
}

// §6.7.1: Net coexisting with variable declarations in the same module.
TEST(ParserSection6, Sec6_7_1_NetCoexistsWithVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  wire [7:0] net_w;\n"
      "  logic [7:0] var_v;\n"
      "  int count;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 3u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(items[0]->data_type.is_net);
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kVarDecl);
  EXPECT_FALSE(items[1]->data_type.is_net);
  EXPECT_EQ(items[2]->kind, ModuleItemKind::kVarDecl);
  EXPECT_FALSE(items[2]->data_type.is_net);
}

// §6.7.1: Wire with range and multiple names.
TEST(ParserSection6, Sec6_7_1_WireRangeMultipleNames) {
  auto r = Parse(
      "module t;\n"
      "  wire [3:0] x, y, z;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 3u);
  for (auto* item : items) {
    EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
    ASSERT_NE(item->data_type.packed_dim_left, nullptr);
    EXPECT_EQ(item->data_type.packed_dim_left->int_val, 3u);
  }
  EXPECT_EQ(items[0]->name, "x");
  EXPECT_EQ(items[1]->name, "y");
  EXPECT_EQ(items[2]->name, "z");
}

// §6.7.1: Tri net with signed qualifier and range.
TEST(ParserSection6, Sec6_7_1_TriSignedWithRange) {
  auto r = Parse(
      "module t;\n"
      "  tri signed [15:0] ts;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTri);
  EXPECT_TRUE(item->data_type.is_signed);
  EXPECT_TRUE(item->data_type.is_net);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 15u);
}

// §6.7.1: Wand with range.
TEST(ParserSection6, Sec6_7_1_WandWithRange) {
  auto r = Parse(
      "module t;\n"
      "  wand [31:0] bus;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kWand);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 31u);
  EXPECT_EQ(item->name, "bus");
}

// §6.7.1: Supply0 with range.
TEST(ParserSection6, Sec6_7_1_Supply0WithRange) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  supply0 [3:0] gnd_bus;\n"
              "endmodule\n"));
}

// §6.7.1: Supply1 with range.
TEST(ParserSection6, Sec6_7_1_Supply1WithRange) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  supply1 [3:0] vdd_bus;\n"
              "endmodule\n"));
}

}  // namespace
