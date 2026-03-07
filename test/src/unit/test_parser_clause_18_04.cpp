// §18.4

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(SourceText, ClassPropertyWithQualifiers) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  randc bit [3:0] y;\n"
      "  static int count;\n"
      "  protected int secret;\n"
      "  local int hidden;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 5u);
  EXPECT_TRUE(members[0]->is_rand);
  EXPECT_EQ(members[0]->name, "x");
  EXPECT_TRUE(members[1]->is_randc);
  EXPECT_EQ(members[1]->name, "y");
  EXPECT_TRUE(members[2]->is_static);
  EXPECT_TRUE(members[3]->is_protected);
  EXPECT_TRUE(members[4]->is_local);
}

}  // namespace
