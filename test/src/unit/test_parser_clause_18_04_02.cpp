// §18.4.2: Randc modifier

#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

using CheckerParseTest = ProgramTestParse;

namespace {

TEST(ParserSection18, RandcMultiDeclarator) {
  auto r = Parse("class C;\n"
                 "  randc bit [2:0] x, y;\n"
                 "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_GE(r.cu->classes[0]->members.size(), 2u);
}
// §8.3 — Randc qualifier
TEST(ParserSection8, RandcQualifier) {
  auto r = Parse("class Die;\n"
                 "  randc bit [2:0] face;\n"
                 "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  ASSERT_GE(r.cu->classes[0]->members.size(), 1u);
  EXPECT_TRUE(r.cu->classes[0]->members[0]->is_randc);
}

} // namespace
