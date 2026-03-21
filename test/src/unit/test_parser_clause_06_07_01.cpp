#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(FormalSyntaxParsing, NetDeclWire) {
  auto r = Parse("module m; wire [3:0] w; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kNetDecl);
}

TEST(TypeDeclParsing, NetDeclWireBasic) {
  auto r = Parse("module m; wire [7:0] data; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_net);
}

TEST(TypeDeclParsing, NetDeclWithDriveStrength) {
  auto r = Parse("module m; wire (strong0, weak1) w; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_NE(item->drive_strength0, 0);
}

TEST(TypeDeclParsing, NetDeclWithDelay) {
  auto r = Parse("module m; wire #5 w; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_NE(item->net_delay, nullptr);
}

TEST(TypeDeclParsing, NetDeclMultipleAssign) {
  auto r = Parse("module m; wire a, b, c; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kNetDecl) count++;
  }
  EXPECT_GE(count, 3);
}

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

TEST(DelayParsing, DelayValuePsIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  parameter delay_val = 5;\n"
      "  wire #delay_val w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto* item = r.cu->modules[0]->items[1];
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->kind, ExprKind::kIdentifier);
}

TEST(DelayParsing, Delay3NetSingleValue) {
  auto r = Parse(
      "module m;\n"
      "  wire #5 w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->int_val, 5u);
  EXPECT_EQ(item->net_delay_fall, nullptr);
  EXPECT_EQ(item->net_delay_decay, nullptr);
}

TEST(DelayParsing, Delay3NetMintypmax) {
  auto r = Parse(
      "module m;\n"
      "  wire #(1:2:3) w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->kind, ExprKind::kMinTypMax);
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

TEST(DeclarationListParsing, ListOfNetDeclAssignmentsMultiple) {
  auto r = Parse("module m; wire a, b, c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kNetDecl) count++;
  }
  EXPECT_GE(count, 3);
}

TEST(DeclarationListParsing, ListOfNetDeclAssignmentsWithUnpackedDim) {
  auto r = Parse("module m; wire a [3:0], b [7:0]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kNetDecl) count++;
  }
  EXPECT_GE(count, 2);
}

TEST(DeclarationRangeParsing, NetWithUnpackedDim) {
  auto r = Parse("module m; wire [7:0] bus [0:3]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
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

TEST(DataTypeParsing, MultipleNetsExplicitType) {
  auto r = Parse(
      "module t;\n"
      "  wire logic a, b, c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 3u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(items[0]->data_type.is_net);
  EXPECT_EQ(items[0]->name, "a");
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(items[1]->data_type.is_net);
  EXPECT_EQ(items[1]->name, "b");
  EXPECT_EQ(items[2]->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(items[2]->data_type.is_net);
  EXPECT_EQ(items[2]->name, "c");
}

TEST(DataTypeParsing, NetWithExplicitBitType) {
  auto r = Parse(
      "module t;\n"
      "  tri bit [3:0] b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_EQ(item->name, "b");
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

TEST(DataTypeParsing, NetImplicitSigned) {
  auto r = Parse(
      "module t;\n"
      "  wire signed [7:0] ws;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_TRUE(item->data_type.is_signed);
  EXPECT_EQ(item->name, "ws");
}

TEST(DataTypeParsing, WireImplicitLogic) {
  auto r = Parse(
      "module t;\n"
      "  wire w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_net);
}

TEST(DataTypeParsing, TriImplicitLogic) {
  auto r = Parse(
      "module t;\n"
      "  tri t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_net);
}

TEST(DataTypeParsing, WandImplicitLogic) {
  auto r = Parse(
      "module t;\n"
      "  wand w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_net);
}

TEST(DataTypeParsing, WireWithRange) {
  auto r = Parse(
      "module t;\n"
      "  wire [15:0] ww;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_NE(item->data_type.packed_dim_left, nullptr);
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

TEST(DataTypeParsing, WireExplicitLogicType) {
  auto r = Parse(
      "module t;\n"
      "  wire logic [7:0] w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
}

TEST(DataTypeParsing, WireIntegerType) {
  auto r = Parse(
      "module t;\n"
      "  wire integer w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
}

TEST(DataTypeParsing, WireTimeType) {
  auto r = Parse(
      "module t;\n"
      "  wire time w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
}

TEST(DataTypeParsing, WireWithPackedStruct) {
  auto r = Parse(
      "module t;\n"
      "  wire struct packed { logic ecc; logic [7:0] data; } memsig;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "memsig");
}

TEST(DataTypeParsing, WireWithTypedef) {
  auto r = Parse(
      "module t;\n"
      "  typedef logic [31:0] addressT;\n"
      "  wire addressT w1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto& items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 2u);
  EXPECT_EQ(items[1]->name, "w1");
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

TEST(DataTypeParsing, TriNetDecl) {
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

TEST(DataTypeParsing, WireDeclaration_Kind) {
  auto r = Parse(
      "module t;\n"
      "  wire [7:0] w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kWire);
}

TEST(DataTypeParsing, WireMultipleNames) {
  auto r = Parse(
      "module t;\n"
      "  wire a, b, c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 3u);
  EXPECT_EQ(items[0]->name, "a");
  EXPECT_EQ(items[1]->name, "b");
  EXPECT_EQ(items[2]->name, "c");
}

TEST(DataTypeParsing, WireDeclaration_Props) {
  auto r = Parse(
      "module t;\n"
      "  wire [7:0] w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_EQ(item->name, "w");
}

TEST(DataTypeParsing, TriDeclaration) {
  auto r = Parse(
      "module t;\n"
      "  tri [3:0] t1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_net);
}

TEST(DataTypeParsing, WireMultipleNamesAllNetDecl) {
  auto r = Parse(
      "module t;\n"
      "  wire a, b, c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 3u);
  for (auto* item : items) {
    EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
    EXPECT_EQ(item->data_type.kind, DataTypeKind::kWire);
    EXPECT_TRUE(item->data_type.is_net);
  }
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

TEST(DataTypeParsing, WireUnpackedDim) {
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

TEST(DataTypeParsing, Supply0WithRange) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  supply0 [3:0] gnd_bus;\n"
              "endmodule\n"));
}

TEST(DataTypeParsing, Supply1WithRange) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  supply1 [3:0] vdd_bus;\n"
              "endmodule\n"));
}

TEST(DataTypeParsing, TriRegDirectlyIsError) {
  EXPECT_FALSE(
      ParseOk("module t;\n"
              "  tri reg r;\n"
              "endmodule\n"));
}

TEST(DataTypeParsing, WireRegDirectlyIsError) {
  EXPECT_FALSE(
      ParseOk("module t;\n"
              "  wire reg p;\n"
              "endmodule\n"));
}

TEST(DataTypeParsing, WandRegDirectlyIsError) {
  EXPECT_FALSE(
      ParseOk("module t;\n"
              "  wand reg w;\n"
              "endmodule\n"));
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

TEST(DataTypeParsing, WorRegDirectlyIsError) {
  EXPECT_FALSE(
      ParseOk("module t;\n"
              "  wor reg w;\n"
              "endmodule\n"));
}

TEST(DataTypeParsing, TriandRegDirectlyIsError) {
  EXPECT_FALSE(
      ParseOk("module t;\n"
              "  triand reg w;\n"
              "endmodule\n"));
}

TEST(DataTypeParsing, TriorRegDirectlyIsError) {
  EXPECT_FALSE(
      ParseOk("module t;\n"
              "  trior reg w;\n"
              "endmodule\n"));
}

TEST(DataTypeParsing, Tri0RegDirectlyIsError) {
  EXPECT_FALSE(
      ParseOk("module t;\n"
              "  tri0 reg r;\n"
              "endmodule\n"));
}

TEST(DataTypeParsing, Tri1RegDirectlyIsError) {
  EXPECT_FALSE(
      ParseOk("module t;\n"
              "  tri1 reg r;\n"
              "endmodule\n"));
}

TEST(DataTypeParsing, Supply0RegDirectlyIsError) {
  EXPECT_FALSE(
      ParseOk("module t;\n"
              "  supply0 reg r;\n"
              "endmodule\n"));
}

TEST(DataTypeParsing, Supply1RegDirectlyIsError) {
  EXPECT_FALSE(
      ParseOk("module t;\n"
              "  supply1 reg r;\n"
              "endmodule\n"));
}

TEST(DataTypeParsing, UwireRegDirectlyIsError) {
  EXPECT_FALSE(
      ParseOk("module t;\n"
              "  uwire reg r;\n"
              "endmodule\n"));
}

TEST(DataTypeParsing, TriregRegDirectlyIsError) {
  EXPECT_FALSE(
      ParseOk("module t;\n"
              "  trireg reg r;\n"
              "endmodule\n"));
}

TEST(DataTypeParsing, Delay3RiseFallDecay) {
  auto r = Parse(
      "module t;\n"
      "  wire #(1, 2, 3) w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->net_delay, nullptr);
  EXPECT_NE(item->net_delay_fall, nullptr);
  EXPECT_NE(item->net_delay_decay, nullptr);
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

TEST(NetDeclarations, WireWithPackedRange) {
  auto r = Parse(
      "module m;\n"
      "  wire [7:0] bus;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kNetDecl);
}

}  // namespace
