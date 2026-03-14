#include "elaborator/type_eval.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(DataTypeParsing, NetsCantBeProcAssigned) {
  auto r = Parse(
      "module t;\n"
      "  wire a;\n"
      "  assign a = 1'b1;\n"
      "  logic b;\n"
      "  initial b = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_GE(r.cu->modules[0]->items.size(), 4u);
}

TEST(DataTypeParsing, VarDrivenByInitialBlock) {
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

TEST(DataTypeParsing, MixedNetAndVarDecls) {
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

  EXPECT_EQ(items[0]->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(items[0]->data_type.is_net);
  EXPECT_EQ(items[2]->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(items[2]->data_type.is_net);

  EXPECT_EQ(items[1]->kind, ModuleItemKind::kVarDecl);
  EXPECT_FALSE(items[1]->data_type.is_net);
  EXPECT_EQ(items[3]->kind, ModuleItemKind::kVarDecl);
  EXPECT_FALSE(items[3]->data_type.is_net);
  EXPECT_EQ(items[4]->kind, ModuleItemKind::kVarDecl);
  EXPECT_FALSE(items[4]->data_type.is_net);
}

TEST(DataTypeParsing, LogicVarDeclKind) {
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

TEST(DataTypeParsing, NetAndVarSameWidthVectors) {
  auto r = Parse(
      "module t;\n"
      "  wire [31:0] net_data;\n"
      "  logic [31:0] var_data;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 2u);

  EXPECT_EQ(items[0]->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(items[0]->data_type.is_net);
  ASSERT_NE(items[0]->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(items[0]->data_type.packed_dim_left->int_val, 31u);

  EXPECT_EQ(items[1]->kind, ModuleItemKind::kVarDecl);
  EXPECT_FALSE(items[1]->data_type.is_net);
  ASSERT_NE(items[1]->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(items[1]->data_type.packed_dim_left->int_val, 31u);
}

}  // namespace
