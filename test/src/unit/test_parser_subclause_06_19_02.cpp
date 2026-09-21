#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

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
  EXPECT_TRUE(ReportedError(r.diags, "expected ']'", 2, "6.19.2"));
}

// §6.19.2's Syntax 6-5 (printed page 119 of ~/IEEE 1800-2023.pdf, A.2.2.1 at
// printed 1182) writes an enum_name_declaration's range as
// `[ integral_number [ : integral_number ] ]`, not as a constant expression,
// and Table 6-10 (printed 121) has N be a positive integral number: `VAL[N]`
// over a parameter N is no range the clause reads, however N would fold.
// Before, Parser::ParseEnumBody in src/parser/parser_aggregate_types.cpp read
// the bound with ParseExpr and accepted any expression, and the elaborator's
// walks, folding the bound against no scope, gave the member neither a
// generated constant nor a backing variable. Each bound is reported where it
// stands: the start bound of `VAL[N]` on line 3 and the end bound of `W[1:N]`
// on line 4.
TEST(DataTypeParsing, EnumRangeBoundNamingAParameterIsReported) {
  auto r = Parse(
      "module m;\n"
      "  localparam N = 3;\n"
      "  typedef enum {VAL[N],\n"
      "                W[1:N]} t;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "enumeration range bound must be an integral number", 3,
      "6.19.2"));
  EXPECT_TRUE(ReportedError(
      r.diags, "enumeration range bound must be an integral number", 4,
      "6.19.2"));
}

// An operator expression over numbers folds to a number but is no
// integral_number of A.8.7, nor is a number in parentheses: `VAL[2+1]` is
// reported on line 2 and `W[(3)]` on line 3.
TEST(DataTypeParsing, EnumRangeBoundThatIsAnExpressionOverNumbersIsReported) {
  auto r = Parse(
      "module m;\n"
      "  typedef enum {VAL[2+1],\n"
      "                W[(3)]} t;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "enumeration range bound must be an integral number", 2,
      "6.19.2"));
  EXPECT_TRUE(ReportedError(
      r.diags, "enumeration range bound must be an integral number", 3,
      "6.19.2"));
}

// A.8.7 spells an integral_number as a decimal, binary, octal or hexadecimal
// number, sized or not, so `VAL[3]`, `W[3:1]`, `X['d3]` and `Y[4'h3]` are
// each the range Syntax 6-5 reads, and the member records both bounds of the
// `N:M` form and the one bound of the others.
TEST(DataTypeParsing, EnumRangeBoundsThatAreIntegralNumbersAreAccepted) {
  auto r = Parse(
      "module m;\n"
      "  typedef enum {VAL[3], W[3:1], X['d3], Y[4'h3]} t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto& members = r.cu->modules[0]->items[0]->typedef_type.enum_members;
  ASSERT_EQ(members.size(), 4u);
  EXPECT_NE(members[0].range_start, nullptr);
  EXPECT_EQ(members[0].range_end, nullptr);
  EXPECT_NE(members[1].range_start, nullptr);
  EXPECT_NE(members[1].range_end, nullptr);
  EXPECT_NE(members[2].range_start, nullptr);
  EXPECT_NE(members[3].range_start, nullptr);
}

}  // namespace
