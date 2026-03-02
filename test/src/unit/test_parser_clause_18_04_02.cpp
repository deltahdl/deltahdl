// §18.4.2: Randc modifier

#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

using CheckerParseTest = ProgramTestParse;

namespace {

TEST(ParserSection18, RandcMultiDeclarator) {
  auto r = Parse(
      "class C;\n"
      "  randc bit [2:0] x, y;\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_GE(r.cu->classes[0]->members.size(), 2u);
}

}  // namespace
