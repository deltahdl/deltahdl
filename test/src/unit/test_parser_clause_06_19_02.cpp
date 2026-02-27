// §6.19.2: Enumerated type ranges

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA221, EnumNameWithRange) {
  // enum_id [ integral_number ]
  auto r = Parse("module m; enum {A[3]} x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& member = r.cu->modules[0]->items[0]->data_type.enum_members[0];
  EXPECT_NE(member.range_start, nullptr);
}

TEST(ParserA221, EnumNameWithRangeColon) {
  // enum_id [ integral_number : integral_number ]
  auto r = Parse("module m; enum {A[0:3] = 10} x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& member = r.cu->modules[0]->items[0]->data_type.enum_members[0];
  EXPECT_NE(member.range_start, nullptr);
  EXPECT_NE(member.range_end, nullptr);
  EXPECT_NE(member.value, nullptr);
}

}  // namespace
