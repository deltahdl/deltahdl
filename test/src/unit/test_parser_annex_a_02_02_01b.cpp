#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

TEST(NetAndVariableTypeParsing, SigningAfterANonIntegerTypeIsReported) {
  auto r = Parse(
      "module m;\n"
      "  real signed r;\n"
      "  string unsigned s;\n"
      "  chandle signed c;\n"
      "  event unsigned e;\n"
      "endmodule\n");
  for (uint32_t line : {2U, 3U, 4U, 5U}) {
    EXPECT_TRUE(ReportedError(
        r.diags, "only an integer vector or integer atom type takes a signing",
        line, "A.2.2.1"));
  }
}

TEST(NetAndVariableTypeParsing, SigningAfterAnIntegerTypeOrALoneNetTypeIsKept) {
  auto r = Parse(
      "module m;\n"
      "  int unsigned u;\n"
      "  logic signed [3:0] v;\n"
      "  wire signed w;\n"
      "  wire logic signed [1:0] x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 4u);
  EXPECT_FALSE(items[0]->data_type.is_signed);
  EXPECT_TRUE(items[1]->data_type.is_signed);
  EXPECT_TRUE(items[2]->data_type.is_signed);
  EXPECT_TRUE(items[3]->data_type.is_signed);
}

TEST(NetAndVariableTypeParsing, EnumBaseOutsideEnumBaseTypeIsReported) {
  auto r = Parse(
      "module m;\n"
      "  enum real {A} e1;\n"
      "  enum string {B} e2;\n"
      "  enum signed {C} e3;\n"
      "  enum logic [1:0][3:0] {D} e4;\n"
      "  enum int [3:0] {E} e5;\n"
      "  enum const int {F} e6;\n"
      "endmodule\n");
  for (uint32_t line : {2U, 3U, 4U}) {
    EXPECT_TRUE(ReportedError(r.diags,
                              "an enumeration's base type is an integer atom "
                              "type, an integer vector type or a type name",
                              line, "A.2.2.1"));
  }
  EXPECT_TRUE(ReportedError(
      r.diags, "an enumeration's base type takes at most one packed dimension",
      5, "A.2.2.1"));
  EXPECT_TRUE(ReportedError(r.diags,
                            "an integer atom type takes no packed dimension as "
                            "an enumeration's base type",
                            6, "A.2.2.1"));
  EXPECT_TRUE(ReportedError(
      r.diags, "an enumeration's base type takes no 'const'", 7, "A.2.2.1"));
}

TEST(NetAndVariableTypeParsing, EnumBaseWithinEnumBaseTypeIsAccepted) {
  auto r = Parse(
      "module m;\n"
      "  typedef bit [3:0] nib_t;\n"
      "  enum {A} a;\n"
      "  enum byte unsigned {B} b;\n"
      "  enum bit signed [3:0] {C} c;\n"
      "  enum logic [1:0] {D} [1:0] d;\n"
      "  enum nib_t {E} e;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(NetAndVariableTypeParsing, MemberWithoutADataTypeIsReported) {
  auto r = Parse(
      "module m;\n"
      "  struct { [3:0] b; bit k; } s1;\n"
      "  struct { signed a; bit k; } s2;\n"
      "  struct { c; bit k; } s3;\n"
      "  union { ; bit k; } s4;\n"
      "endmodule\n");
  for (uint32_t line : {2U, 3U, 4U, 5U}) {
    EXPECT_TRUE(ReportedError(
        r.diags, "a structure or union member names a data type or void", line,
        "A.2.2.1"));
  }
}

TEST(NetAndVariableTypeParsing, MemberNamingItsDataTypeIsRead) {
  auto r = Parse(
      "module m;\n"
      "  typedef bit [3:0] nib_t;\n"
      "  struct { bit [3:0] b; logic signed a; nib_t n; } s;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto& members = r.cu->modules[0]->items[1]->data_type.struct_members;
  ASSERT_EQ(members.size(), 3u);
  EXPECT_EQ(members[0].type_kind, DataTypeKind::kBit);
  EXPECT_EQ(members[1].type_kind, DataTypeKind::kLogic);
  EXPECT_TRUE(members[1].is_signed);
  EXPECT_EQ(members[2].type_kind, DataTypeKind::kNamed);
}

TEST(NetAndVariableTypeParsing, StructureMemberOfATypeReference) {
  auto r = Parse(
      "module m;\n"
      "  int x;\n"
      "  struct { type(x) f; bit k; } s;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto& members = r.cu->modules[0]->items[1]->data_type.struct_members;
  ASSERT_EQ(members.size(), 2u);
  EXPECT_EQ(members[0].name, "f");
  ASSERT_NE(members[0].nested_type, nullptr);
  EXPECT_NE(members[0].nested_type->type_ref_expr, nullptr);
  EXPECT_EQ(members[1].name, "k");
}

}  // namespace
