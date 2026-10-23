// Tests of the A.2.2.1 productions whose departures the parser reports: the
// data types a signing follows, the forms an enumeration's base type takes,
// and the data type a structure or union member names.

#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

// A.2.2.1 writes a signing after an integer vector type and after an integer
// atom type, and after no other data type, so one after real, string, chandle
// or event is reported where it stands.
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

// The integer types keep their signing, and so does a net type keyword with no
// data type keyword after it, the signing there opening the implicit data type
// of A.2.1.3's net declaration.
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

// A.2.2.1's enum_base_type is an integer atom type with an optional signing,
// an integer vector type with an optional signing and at most one packed
// dimension, or a type name with at most one packed dimension. A non-integer
// type, string, a signing alone, a second packed dimension, a packed dimension
// on an atom and a leading const are none of the three.
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

// Each of the three forms stands, as does no base at all. The dimension after
// the body packs the enumeration rather than its base.
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

// A.2.2.1's struct_union_member names a data_type or void before the member's
// names, and the body holds members and no null item. A signing or packed
// dimension alone, a bare name and a lone `;` name none, whether the parse can
// read a member out of what follows or not.
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

// A member that names its data type, a keyword type with its signing or a
// typedef name, is read as written.
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

// A.2.2.1's struct_union_member writes a data_type before the member's names,
// and a type_reference is one (§6.23), kept whole on the member for the
// elaborator to resolve. A member is neither a net nor a variable declaration,
// so no keyword comes before it.
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
