#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA221, EnumNameWithRange) {
  auto r = Parse("module m; enum {A[3]} x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& member = r.cu->modules[0]->items[0]->data_type.enum_members[0];
  EXPECT_NE(member.range_start, nullptr);
}

TEST(ParserA221, EnumNameWithRangeColon) {
  auto r = Parse("module m; enum {A[0:3] = 10} x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& member = r.cu->modules[0]->items[0]->data_type.enum_members[0];
  EXPECT_NE(member.range_start, nullptr);
  EXPECT_NE(member.range_end, nullptr);
  EXPECT_NE(member.value, nullptr);
}

TEST(ParserSection6, EnumRangeNOnly) {
  auto r = Parse(
      "module m;\n"
      "  typedef enum {add=10, sub[5], jmp[6:8]} E1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection6, EnumRangeNM) {
  auto r = Parse(
      "module m;\n"
      "  enum {register[2] = 1, register[2:4] = 10} vr;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
