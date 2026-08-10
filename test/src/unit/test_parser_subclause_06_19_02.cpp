#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(DataTypeParsing, EnumRangeNOnly) {
  auto r = Parse(
      "module m;\n"
      "  typedef enum {add=10, sub[5], jmp[6:8]} E1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(DataTypeParsing, EnumRangeNM) {
  auto r = Parse(
      "module m;\n"
      "  enum {register[2] = 1, register[2:4] = 10} vr;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(DataTypeParsing, EnumRangeNWithValue) {
  auto r = Parse("module m; enum {A[3] = 5} x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& member = r.cu->modules[0]->items[0]->data_type.enum_members[0];
  EXPECT_NE(member.range_start, nullptr);
  EXPECT_EQ(member.range_end, nullptr);
  EXPECT_NE(member.value, nullptr);
}

TEST(DataTypeParsing, EnumRangeNMWithValue) {
  // The name[N:M] = C form must capture all three optional pieces on the
  // member: the start bound, the end bound, and the assigned value.
  auto r = Parse("module m; enum {A[2:4] = 7} x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& member = r.cu->modules[0]->items[0]->data_type.enum_members[0];
  EXPECT_NE(member.range_start, nullptr);
  EXPECT_NE(member.range_end, nullptr);
  EXPECT_NE(member.value, nullptr);
}

TEST(DataTypeParsing, EnumRangeDecrementing) {
  auto r = Parse("module m; enum {A[5:3]} x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& member = r.cu->modules[0]->items[0]->data_type.enum_members[0];
  EXPECT_NE(member.range_start, nullptr);
  EXPECT_NE(member.range_end, nullptr);
}

// §6.19.2, Syntax 6-1: an enum_name_declaration writes its range as
// `[ integral_number [ : integral_number ] ]`, so the closing bracket is
// obligatory. The enum_name_declaration itself is §6.19, and the range is the
// one part of it §6.19.2 states separately; the subclause on this report is
// what tells a broken range from a broken member list. The space before the `}`
// puts the report a number and white space downstream of the lexer's
// base-specifier lookahead, which is where a column drifts if that lookahead
// leaves the counter where it read to.
TEST(DataTypeParsing, MalformedEnumRangeNames6_19_2) {
  auto r = Parse(
      "module m;\n"
      "  typedef enum { a[3 } e;\n"
      "endmodule\n");
  ASSERT_FALSE(r.diags.empty());
  EXPECT_EQ(r.diags.front().subclause, "6.19.2");
  EXPECT_EQ(r.diags.front().loc.line, 2u);
  EXPECT_EQ(r.diags.front().loc.column, 22u);
}

}  // namespace
