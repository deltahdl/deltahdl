

#include <gtest/gtest.h>

#include <string>

#include "common/diagnostic.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "model_net_declaration.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

TEST(VectorNetAccessibility, ScalaredWithExplicitType) {
  auto r = Parse(
      "module t;\n"
      "  wire scalared logic [7:0] s;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_TRUE(item->data_type.is_scalared);
  EXPECT_EQ(item->name, "s");
}

TEST(VectorNetAccessibility, WireVectoredQualifier) {
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

TEST(VectorNetAccessibility, WireScalaredQualifier) {
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

TEST(VectorNetAccessibility, Tri1ScalaredBus) {
  auto r = Parse(
      "module t;\n"
      "  tri1 scalared [63:0] bus64;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTri1);
  EXPECT_TRUE(item->data_type.is_scalared);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 63u);
}

TEST(VectorNetAccessibility, TriVectoredData) {
  auto r = Parse(
      "module t;\n"
      "  tri vectored [31:0] data;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTri);
  EXPECT_TRUE(item->data_type.is_vectored);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 31u);
}

TEST(VectorNetAccessibility, VectoredWithoutPackedDim) {
  NetDeclInfo info;
  info.is_vectored = true;
  info.packed_dim_count = 0;
  EXPECT_FALSE(ValidateNetDecl(info));
}

TEST(VectorNetAccessibility, ScalaredWithoutPackedDim) {
  NetDeclInfo info;
  info.is_scalared = true;
  info.packed_dim_count = 0;
  EXPECT_FALSE(ValidateNetDecl(info));
}

TEST(VectorNetAccessibility, WireVectoredRegOk) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  wire vectored reg [7:0] r;\n"
              "endmodule\n"));
}

TEST(VectorNetAccessibility, VectoredWithExplicitType) {
  auto r = Parse(
      "module t;\n"
      "  wire vectored logic [7:0] v;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_TRUE(item->data_type.is_vectored);
  EXPECT_EQ(item->name, "v");
}

TEST(VectorNetAccessibility, WandVectoredOk) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  wand vectored [7:0] w;\n"
              "endmodule\n"));
}

TEST(VectorNetAccessibility, WorScalaredOk) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  wor scalared [7:0] w;\n"
              "endmodule\n"));
}

TEST(VectorNetAccessibility, PlainWireNeitherFlag) {
  auto r = Parse(
      "module t;\n"
      "  wire [7:0] w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_FALSE(item->data_type.is_vectored);
  EXPECT_FALSE(item->data_type.is_scalared);
}

// §6.9.2 gives vectored and scalared to vector net declarations, and the
// variable declaration grammar of §6.8 admits neither, so the keyword after a
// variable's type is reported under §6.9.2 rather than as the identifier the
// declarator list did not find. sv-tests' 6.9.2--vector_vectored_inv.sv writes
// `logic vectored` for a vectored net, and a report under §6.8 scored it FAIL.
TEST(VectorNetAccessibility, VectoredAfterVariableTypeIsAClause692Report) {
  auto r = Parse(
      "module top();\n"
      "  logic vectored [15:0] a = 0;\n"
      "  assign a[1] = 1;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "'vectored' shall be used in a vector net declaration and 'logic' "
      "declares no net",
      2, "6.9.2"));
  for (const auto& d : r.diags) {
    EXPECT_EQ(d.subclause, "6.9.2") << d.message;
  }
}

TEST(VectorNetAccessibility, ScalaredAfterVariableTypeIsAClause692Report) {
  auto r = Parse(
      "module top();\n"
      "  bit scalared [7:0] b;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "'scalared' shall be used in a vector net declaration and 'bit' "
      "declares no net",
      2, "6.9.2"));
  for (const auto& d : r.diags) {
    EXPECT_EQ(d.subclause, "6.9.2") << d.message;
  }
}

// The keyword is taken with the type, so the declarators after it are parsed
// in step: the declaration still lands as a variable named as written.
TEST(VectorNetAccessibility, VectoredAfterVariableTypeLeavesTheDeclarator) {
  auto r = Parse(
      "module top();\n"
      "  logic vectored [15:0] a = 0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_FALSE(item->data_type.is_net);
  EXPECT_FALSE(item->data_type.is_vectored);
  EXPECT_EQ(item->name, "a");
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 15u);
}

}  // namespace
