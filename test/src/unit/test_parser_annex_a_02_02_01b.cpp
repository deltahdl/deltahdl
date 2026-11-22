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

TEST(NetAndVariableTypeParsing, DISABLED_SoftOrTaggedAfterStructIsReported) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct tagged { int a; } t1;\n"
      "  struct tagged packed { int a; } s1;\n"
      "  typedef struct soft { int a; } t2;\n"
      "  struct soft packed { int a; } s2;\n"
      "endmodule\n");
  for (uint32_t line : {2U, 3U, 4U, 5U}) {
    EXPECT_TRUE(ReportedError(r.diags, "only a union takes soft or tagged",
                              line, "A.2.2.1"));
  }
  EXPECT_EQ(r.diags.size(), 4u);
}

TEST(NetAndVariableTypeParsing, SoftOrTaggedAfterUnionIsAccepted) {
  auto r = Parse(
      "module m;\n"
      "  union tagged { int a; } u1;\n"
      "  union soft { int a; } u2;\n"
      "endmodule\n");
  EXPECT_TRUE(r.diags.empty());
}

TEST(NetAndVariableTypeParsing,
     DISABLED_MemberOpeningWithAQualifierIsReported) {
  auto r = Parse(
      "module m;\n"
      "  struct { const int a; } s1;\n"
      "  union { const int a; } u1;\n"
      "  struct { var int a; } s2;\n"
      "  union { var int a; } u2;\n"
      "  struct { static int a; } s3;\n"
      "  union { static int a; } u3;\n"
      "  struct { automatic int a; } s4;\n"
      "  union { automatic int a; } u4;\n"
      "endmodule\n");
  for (uint32_t line = 2; line <= 9; ++line) {
    EXPECT_TRUE(
        ReportedError(r.diags, "a structure or union member", line, "A.2.2.1"));
  }
  EXPECT_EQ(r.diags.size(), 8u);
}

TEST(NetAndVariableTypeParsing, MemberOpeningWithItsDataTypeIsAccepted) {
  auto r = Parse(
      "module m;\n"
      "  struct { int a; } s;\n"
      "  union { int a; } u;\n"
      "endmodule\n");
  EXPECT_TRUE(r.diags.empty());
}

TEST(NetAndVariableTypeParsing, EnumTypeNameBaseTakesOnePackedDimension) {
  auto r = Parse(
      "module m;\n"
      "  typedef bit [3:0] nib_t;\n"
      "  typedef logic my_logic_t;\n"
      "  enum nib_t [1:0][1:0] {A} e;\n"
      "  enum my_logic_t [3:0] {B, C, D} e2;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "an enumeration's base type takes at most one packed dimension",
      4, "A.2.2.1"));
  EXPECT_EQ(r.diags.size(), 1u);
}

TEST(NetAndVariableTypeParsing, DISABLED_EnumScopedBaseIsReported) {
  auto r = Parse(
      "package p; typedef bit [3:0] t; endpackage\n"
      "class C; typedef bit [3:0] t; endclass\n"
      "module m;\n"
      "  enum p::t {A} e1;\n"
      "  enum C::t {B} e2;\n"
      "endmodule\n");
  for (uint32_t line : {4U, 5U}) {
    EXPECT_TRUE(ReportedError(r.diags,
                              "an enumeration's base type names no package or "
                              "class scope",
                              line, "A.2.2.1"));
  }
  EXPECT_EQ(r.diags.size(), 2u);
}

TEST(NetAndVariableTypeParsing, EnumBaseImportedFromAPackageIsAccepted) {
  auto r = Parse(
      "package p; typedef bit [3:0] t; endpackage\n"
      "module m;\n"
      "  import p::t;\n"
      "  enum t {A} e;\n"
      "endmodule\n");
  EXPECT_TRUE(r.diags.empty());
}

TEST(NetAndVariableTypeParsing, EnumBaseTypedefOfAClassTypeIsAccepted) {
  auto r = Parse(
      "class C; typedef bit [3:0] t; endclass\n"
      "module m;\n"
      "  typedef C::t ct;\n"
      "  enum ct {A} e;\n"
      "endmodule\n");
  EXPECT_TRUE(r.diags.empty());
}

TEST(NetAndVariableTypeParsing, DISABLED_SigningAfterATypeNameIsReported) {
  auto r = Parse(
      "package p; typedef bit [3:0] t; endpackage\n"
      "module m;\n"
      "  typedef bit [3:0] my_t;\n"
      "  my_t signed x;\n"
      "  p::t signed y;\n"
      "endmodule\n");
  for (uint32_t line : {4U, 5U}) {
    EXPECT_TRUE(ReportedError(
        r.diags, "only an integer vector or integer atom type takes a signing",
        line, "A.2.2.1"));
  }
  EXPECT_EQ(r.diags.size(), 2u);
}

TEST(NetAndVariableTypeParsing, TypeNameWithoutASigningIsAccepted) {
  auto r = Parse(
      "package p; typedef bit [3:0] t; endpackage\n"
      "module m;\n"
      "  typedef bit [3:0] my_t;\n"
      "  my_t x;\n"
      "  p::t y;\n"
      "endmodule\n");
  EXPECT_TRUE(r.diags.empty());
}

TEST(NetAndVariableTypeParsing, DISABLED_ASecondSigningIsReported) {
  auto r = Parse(
      "module m;\n"
      "  logic signed unsigned x;\n"
      "  int unsigned signed i;\n"
      "  logic signed y;\n"
      "  int unsigned j;\n"
      "endmodule\n");
  for (uint32_t line : {2U, 3U}) {
    EXPECT_TRUE(
        ReportedError(r.diags, "takes at most one signing", line, "A.2.2.1"));
  }
  EXPECT_EQ(r.diags.size(), 2u);
}

TEST(NetAndVariableTypeParsing, DISABLED_NetTypeAfterVarIsReported) {
  auto r = Parse(
      "module m(input var wire a); endmodule\n"
      "module n(a);\n"
      "  input var tri a;\n"
      "  var wire x;\n"
      "endmodule\n");
  for (uint32_t line : {1U, 3U, 4U}) {
    EXPECT_TRUE(ReportedError(r.diags, "net type", line, "A.2.2.1"));
  }
  EXPECT_EQ(r.diags.size(), 3u);
}

TEST(NetAndVariableTypeParsing, DataTypeAfterVarIsAccepted) {
  auto r = Parse(
      "module m(input var logic a); endmodule\n"
      "module n(a);\n"
      "  input var logic a;\n"
      "  var logic x;\n"
      "endmodule\n");
  EXPECT_TRUE(r.diags.empty());
}

TEST(NetAndVariableTypeParsing,
     DISABLED_ACastTypeOutsideCastingTypeIsReported) {
  auto r = Parse(
      "module m;\n"
      "  int e;\n"
      "  initial begin\n"
      "    e = logic [7:0]'(e);\n"
      "    e = int unsigned'(e);\n"
      "    e = chandle'(e);\n"
      "    e = event'(e);\n"
      "    e = struct packed { bit a; }'(e);\n"
      "    e = union packed { bit a; }'(e);\n"
      "    e = enum bit {A, B}'(e);\n"
      "  end\n"
      "endmodule\n");
  for (uint32_t line = 4; line <= 10; ++line) {
    EXPECT_TRUE(ReportedError(r.diags, "casting type", line, "A.2.2.1"));
  }
  EXPECT_EQ(r.diags.size(), 7u);
}

TEST(NetAndVariableTypeParsing, ACastTypeWithinCastingTypeIsAccepted) {
  auto r = Parse(
      "module m;\n"
      "  typedef logic [7:0] l8_t;\n"
      "  typedef struct packed { bit a; } s_t;\n"
      "  int e;\n"
      "  string s;\n"
      "  initial begin\n"
      "    e = l8_t'(e);\n"
      "    e = unsigned'(e);\n"
      "    e = int'(e);\n"
      "    s = string'(e);\n"
      "    e = s_t'(e);\n"
      "    e = type(bit [11:0])'(e);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(r.diags.empty());
}

TEST(NetAndVariableTypeParsing, DISABLED_ASigningBeforePackedIsReported) {
  auto r = Parse(
      "module m;\n"
      "  struct signed packed { bit a; } s;\n"
      "  struct packed signed { bit a; } t;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "signing", 2, "A.2.2.1"));
  EXPECT_EQ(r.diags.size(), 1u);
}

TEST(NetAndVariableTypeParsing, DISABLED_AnEmptyBodyIsReported) {
  auto r = Parse(
      "module m;\n"
      "  struct {} s;\n"
      "  union {} u;\n"
      "  enum {} e;\n"
      "  struct { int a; } s2;\n"
      "  enum {A} e2;\n"
      "endmodule\n");
  for (uint32_t line : {2U, 3U, 4U}) {
    EXPECT_TRUE(ReportedError(r.diags, "at least one", line, "A.2.2.1"));
  }
  EXPECT_EQ(r.diags.size(), 3u);
}

TEST(NetAndVariableTypeParsing,
     DISABLED_APackedDimensionAfterAVirtualInterfaceIsReported) {
  auto r = Parse(
      "interface I; endinterface\n"
      "module m;\n"
      "  virtual I [3:0] v;\n"
      "  virtual I w;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "packed dimension", 3, "A.2.2.1"));
  EXPECT_EQ(r.diags.size(), 1u);
}

TEST(NetAndVariableTypeParsing,
     DISABLED_ATypedefOfConstOrAnImplicitTypeIsReported) {
  auto r = Parse(
      "module m;\n"
      "  typedef const int t;\n"
      "  typedef signed [3:0] u;\n"
      "  typedef [3:0] w;\n"
      "  typedef int x;\n"
      "  typedef logic signed [3:0] y;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "const", 2, "A.2.2.1"));
  for (uint32_t line : {3U, 4U}) {
    EXPECT_TRUE(ReportedError(r.diags, "data type", line, "A.2.2.1"));
  }
  EXPECT_EQ(r.diags.size(), 3u);
}

TEST(NetAndVariableTypeParsing,
     DISABLED_AnInterfaceClassThroughAClassScopeIsReported) {
  auto r = Parse(
      "package p;\n"
      "  interface class I; endclass\n"
      "  class Outer; interface class I; endclass endclass\n"
      "endpackage\n"
      "class Outer; interface class I; endclass endclass\n"
      "class C implements Outer::I; endclass\n"
      "class D implements p::Outer::I; endclass\n"
      "interface class X extends Outer::I; endclass\n");
  for (uint32_t line : {6U, 7U, 8U}) {
    EXPECT_TRUE(ReportedError(r.diags, "interface class", line, "A.2.2.1"));
  }
  EXPECT_EQ(r.diags.size(), 3u);
}

TEST(NetAndVariableTypeParsing, AnInterfaceClassThroughAPackageIsAccepted) {
  auto r = Parse(
      "package p; interface class I; endclass endpackage\n"
      "package q; interface class A; endclass endpackage\n"
      "class C implements p::I; endclass\n"
      "interface class X extends q::A; endclass\n");
  EXPECT_TRUE(r.diags.empty());
}

TEST(NetAndVariableTypeParsing,
     NearestFormsOfAnAggregateAndATypedefAreAccepted) {
  auto r = Parse(
      "interface I; endinterface\n"
      "module m;\n"
      "  struct packed signed { bit a; } s;\n"
      "  struct { int a; } s2;\n"
      "  enum {A} e;\n"
      "  virtual I w;\n"
      "  typedef int x;\n"
      "  typedef logic signed [3:0] y;\n"
      "endmodule\n");
  EXPECT_TRUE(r.diags.empty());
}

}  // namespace
