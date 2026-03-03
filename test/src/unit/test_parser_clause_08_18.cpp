// §8.18: Data hiding and encapsulation

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserSection8, ClassWithQualifiersLocalProtected) {
  auto r = Parse(
      "class MyClass;\n"
      "  local int secret;\n"
      "  protected int hidden;\n"
      "  static int shared;\n"
      "  rand int random_val;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  ASSERT_GE(cls->members.size(), 4u);
  EXPECT_TRUE(cls->members[0]->is_local);
  EXPECT_TRUE(cls->members[1]->is_protected);
}

}  // namespace
