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

TEST(DataTypeParsing, MalformedEnumRangeNames6_19_2) {
  auto r = Parse(
      "module m;\n"
      "  typedef enum { a[3 } e;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ']'", 2, "6.19.2"));
}

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
