#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

TEST(StrengthParsing, DriveStrengthOnTri) {
  auto r = Parse(
      "module m;\n"
      "  tri (strong0, strong1) t;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->drive_strength0, 4u);
  EXPECT_EQ(item->drive_strength1, 4u);
}

TEST(StrengthParsing, DriveStrengthOnWand) {
  auto r = Parse(
      "module m;\n"
      "  wand (pull0, pull1) w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->drive_strength0, 3u);
  EXPECT_EQ(item->drive_strength1, 3u);
}

TEST(DeclarationListParsing, ListOfNetDeclAssignmentsSingle) {
  auto r = Parse("module m; wire [7:0] data; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kNetDecl) count++;
  }
  EXPECT_EQ(count, 1);
}

TEST(DataTypeParsing, WireWithUserDefinedType) {
  auto r = Parse(
      "module t;\n"
      "  typedef logic [31:0] addressT;\n"
      "  wire addressT w1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 2u);
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(items[1]->data_type.is_net);
  EXPECT_EQ(items[1]->data_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(items[1]->data_type.type_name, "addressT");
  EXPECT_EQ(items[1]->name, "w1");
}

TEST(DataTypeParsing, WireDriveStrengthReversedOrder) {
  auto r = Parse(
      "module t;\n"
      "  wire (pull1, weak0) w = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);

  EXPECT_EQ(item->drive_strength0, 2u);
  EXPECT_EQ(item->drive_strength1, 3u);
}

TEST(DataTypeParsing, WireWithPackedStructType) {
  auto r = Parse(
      "module t;\n"
      "  wire struct packed { logic ecc; logic [7:0] data; } memsig;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_EQ(item->name, "memsig");
}

TEST(DataTypeParsing, DriveStrengthWithExplicitType) {
  auto r = Parse(
      "module t;\n"
      "  wire (strong0, weak1) logic [7:0] w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_EQ(item->name, "w");
}

TEST(DataTypeParsing, WirePackedDims) {
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

TEST(DataTypeParsing, WireUnpackedDims) {
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

TEST(DataTypeParsing, MultipleWireDecls) {
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

TEST(DataTypeParsing, TriWithRange) {
  auto r = Parse(
      "module t;\n"
      "  tri [7:0] t1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTri);
  EXPECT_TRUE(item->data_type.is_net);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 7u);
  ASSERT_NE(item->data_type.packed_dim_right, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_right->int_val, 0u);
}

TEST(DataTypeParsing, WireExplicitLogicNoErrors) {
  auto r = Parse(
      "module t;\n"
      "  wire logic [7:0] w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_EQ(item->name, "w");
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 7u);
}

TEST(DataTypeParsing, WireNetDeclKind) {
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

TEST(DataTypeParsing, WireSignedQualifier) {
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

TEST(DataTypeParsing, WireWithBitType) {
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

TEST(DataTypeParsing, WireWithDelay) {
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

TEST(DataTypeParsing, MixedNetTypesInModule) {
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

TEST(DataTypeParsing, WirePackedAndUnpackedDims) {
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

TEST(DataTypeParsing, WireDriveStrength) {
  auto r = Parse(
      "module t;\n"
      "  wire (strong0, pull1) w = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);

  EXPECT_EQ(item->drive_strength0, 4u);
  EXPECT_EQ(item->drive_strength1, 3u);
}

TEST(DataTypeParsing, NetCoexistsWithVarDecl) {
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

TEST(DataTypeParsing, WireRangeMultipleNames) {
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

TEST(DataTypeParsing, TriSignedWithRange) {
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

TEST(DataTypeParsing, WandWithRange) {
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

TEST(DataTypeParsing, TriRegDirectlyIsError) {
  auto r = Parse(
      "module t;\n"
      "  tri reg r;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "'reg' cannot come right after a net type keyword", 2, "6.7.1"));
}

TEST(DataTypeParsing, WireRegDirectlyIsError) {
  auto r = Parse(
      "module t;\n"
      "  wire reg p;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "'reg' cannot come right after a net type keyword", 2, "6.7.1"));
}

TEST(DataTypeParsing, WireDriveStrengthRegOk) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  wire (strong0, pull1) reg r = 1'b0;\n"
              "endmodule\n"));
}

TEST(DataTypeParsing, IdentifierStartingWithRegOk) {
  auto r = Parse(
      "module t;\n"
      "  wire reg_name;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->name, "reg_name");
}

TEST(DataTypeParsing, PortNetTypeFollowedByRegIsError) {
  auto r = Parse("module m(inout wire reg p); endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "'reg' cannot come right after a net type keyword", 1, "6.7.1"));
}

TEST(StrengthParsing, DriveStrengthSupply0Weak1) {
  auto r = Parse(
      "module m;\n"
      "  wire (supply0, weak1) w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->drive_strength0, 5u);
  EXPECT_EQ(item->drive_strength1, 2u);
}

TEST(StrengthParsing, DriveStrengthWeak0Weak1) {
  auto r = Parse(
      "module m;\n"
      "  wire (weak0, weak1) w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->drive_strength0, 2u);
  EXPECT_EQ(item->drive_strength1, 2u);
}

TEST(StrengthParsing, DriveStrengthHighz0Strong1) {
  auto r = Parse(
      "module m;\n"
      "  wire (highz0, strong1) w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->drive_strength0, 1u);
  EXPECT_EQ(item->drive_strength1, 4u);
}

TEST(StrengthParsing, DriveStrengthSupply0Supply1) {
  auto r = Parse(
      "module m;\n"
      "  wire (supply0, supply1) w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->drive_strength0, 5u);
  EXPECT_EQ(item->drive_strength1, 5u);
}

TEST(StrengthParsing, DriveStrengthHighz1Pull0) {
  auto r = Parse(
      "module m;\n"
      "  wire (highz1, pull0) w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->drive_strength0, 3u);
  EXPECT_EQ(item->drive_strength1, 1u);
}

TEST(StrengthParsing, NetDeclNoDriveStrengthDefault) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->drive_strength0, 0u);
  EXPECT_EQ(item->drive_strength1, 0u);
}

TEST(InterconnectParsing, PlainInterconnectOk) {
  auto r = Parse("module m; interconnect w; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_interconnect);
}

TEST(InterconnectParsing, PackedDimensionOk) {
  auto r = Parse("module m; interconnect [3:0] w; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_interconnect);
  EXPECT_NE(item->data_type.packed_dim_left, nullptr);
}

TEST(InterconnectParsing, UnpackedDimensionOk) {
  auto r = Parse("module m; interconnect w [0:3]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_interconnect);
  EXPECT_FALSE(item->unpacked_dims.empty());
}

TEST(InterconnectParsing, DataTypeIsError) {
  auto r = Parse("module m; interconnect logic w; endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got 'logic'", 1, "6.7"));
}

TEST(InterconnectParsing, StrengthSpecIsError) {
  auto drive =
      Parse("module m; interconnect (strong0, strong1) w; endmodule\n");
  EXPECT_TRUE(
      ReportedError(drive.diags, "expected identifier, got '('", 1, "6.7"));
  auto charge = Parse("module m; interconnect (small) w; endmodule\n");
  EXPECT_TRUE(
      ReportedError(charge.diags, "expected identifier, got '('", 1, "6.7"));
}

TEST(DataTypeParsing, WireNamedTypeWithPackedDim) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed { logic [7:0] opcode; logic [23:0] imm; }"
      " instruction_t;\n"
      "  wire instruction_t [1:0] v;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 2u);
  auto* item = items[1];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(item->data_type.type_name, "instruction_t");
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  ASSERT_NE(item->data_type.packed_dim_right, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 1u);
  EXPECT_EQ(item->data_type.packed_dim_right->int_val, 0u);
  EXPECT_TRUE(item->data_type.extra_packed_dims.empty());
  EXPECT_EQ(item->name, "v");
  EXPECT_TRUE(item->unpacked_dims.empty());
}

TEST(DataTypeParsing, WireNamedTypeWithTwoPackedDims) {
  auto r = Parse(
      "module m;\n"
      "  typedef logic [3:0] nib_t;\n"
      "  wire nib_t [1:0] [2:0] v;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 2u);
  auto* item = items[1];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kNamed);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 1u);
  ASSERT_EQ(item->data_type.extra_packed_dims.size(), 1u);
  EXPECT_EQ(item->data_type.extra_packed_dims[0].first->int_val, 2u);
  EXPECT_EQ(item->data_type.extra_packed_dims[0].second->int_val, 0u);
  EXPECT_EQ(item->name, "v");
  EXPECT_TRUE(item->unpacked_dims.empty());
}

TEST(DataTypeParsing, WireNamedTypeWithUnpackedDim) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed { logic [7:0] opcode; logic [23:0] imm; }"
      " instruction_t;\n"
      "  wire instruction_t u [2];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 2u);
  auto* item = items[1];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(item->data_type.type_name, "instruction_t");
  EXPECT_EQ(item->data_type.packed_dim_left, nullptr);
  EXPECT_TRUE(item->data_type.extra_packed_dims.empty());
  EXPECT_EQ(item->name, "u");
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  EXPECT_EQ(item->unpacked_dims[0]->int_val, 2u);
}

TEST(DataTypeParsing, WireImplicitTypeNameWithUnpackedDim) {
  auto r = Parse(
      "module m;\n"
      "  wire w [2];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_NE(item->data_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->name, "w");
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  EXPECT_EQ(item->unpacked_dims[0]->int_val, 2u);
}

TEST(DataTypeParsing, WireLogicTwoPackedDims) {
  auto r = Parse(
      "module m;\n"
      "  wire logic [3:0] [1:0] y;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 3u);
  ASSERT_EQ(item->data_type.extra_packed_dims.size(), 1u);
  EXPECT_EQ(item->data_type.extra_packed_dims[0].first->int_val, 1u);
  EXPECT_EQ(item->name, "y");
  EXPECT_TRUE(item->unpacked_dims.empty());
}

constexpr const char* kRegAfterNetType =
    "'reg' cannot come right after a net type keyword";

TEST(DataTypeParsing, EveryNetTypeKeywordFollowedByRegIsError) {
  for (const char* net_type : {"wand", "wor", "triand", "trior", "tri0", "tri1",
                               "trireg", "supply0", "supply1", "uwire"}) {
    auto r =
        Parse(std::string("module t;\n  ") + net_type + " reg r;\nendmodule\n");
    EXPECT_TRUE(ReportedError(r.diags, kRegAfterNetType, 2, "6.7.1"))
        << net_type;
  }
}

TEST(DataTypeParsing, RegAfterAChargeStrengthOrVectoredIsAccepted) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  trireg (small) reg t;\n"
              "  wire vectored reg [3:0] v;\n"
              "endmodule\n"));
}

TEST(DataTypeParsing, RegAfterANetTypeOnAnInputOutputOrNonAnsiPortIsError) {
  EXPECT_TRUE(ReportedError(Parse("module t(input wire reg a);\n"
                                  "endmodule\n")
                                .diags,
                            kRegAfterNetType, 1, "6.7.1"));
  EXPECT_TRUE(ReportedError(Parse("module t(output tri reg b);\n"
                                  "endmodule\n")
                                .diags,
                            kRegAfterNetType, 1, "6.7.1"));
  EXPECT_TRUE(ReportedError(Parse("module t(a);\n"
                                  "  input wire reg a;\n"
                                  "endmodule\n")
                                .diags,
                            kRegAfterNetType, 2, "6.7.1"));
  EXPECT_TRUE(
      ParseOk("module t(input wire logic a, output tri logic b);\n"
              "endmodule\n"
              "module u(a);\n"
              "  input wire logic a;\n"
              "endmodule\n"));
}

TEST(DataTypeParsing, RegAfterANetTypeIsErrorInEveryPlace) {
  struct Place {
    const char* src;
    uint32_t line;
  };
  for (const Place& place : {
           Place{"interface t;\n  wire reg r;\nendinterface\n", 2},
           Place{"program t;\n  wire reg r;\nendprogram\n", 2},
           Place{"module t;\n  if (1) begin : g\n    wire reg r;\n  end\n"
                 "endmodule\n",
                 3},
           Place{"package t;\n  wire reg r;\nendpackage\n", 2},
           Place{"wire reg r;\n", 1},
       }) {
    EXPECT_TRUE(ReportedError(Parse(place.src).diags, kRegAfterNetType,
                              place.line, "6.7.1"))
        << place.src;
  }
  EXPECT_TRUE(
      ParseOk("interface i;\n  wire logic r;\nendinterface\n"
              "program p;\n  wire logic r;\nendprogram\n"
              "module m;\n  if (1) begin : g\n    wire logic r;\n  end\n"
              "endmodule\n"
              "package k;\n  wire logic r;\nendpackage\n"
              "wire logic r;\n"));
}

}  // namespace
