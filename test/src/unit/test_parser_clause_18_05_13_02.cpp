// §18.5.13.2: Disabling soft constraints

#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

using CheckerParseTest = ProgramTestParse;

namespace {

// Constraint implication and disable soft
TEST(SourceText, ConstraintImplicationDisableSoft) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  rand int y;\n"
      "  constraint ic {\n"
      "    x > 0 -> y > 0;\n"
      "    disable soft x;\n"
      "  }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->members[2]->name, "ic");
}

}  // namespace
