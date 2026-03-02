// §18.5.2: Constraint inheritance

#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

using CheckerParseTest = ProgramTestParse;

namespace {

// constraint_declaration with dynamic_override_specifiers (§8.20)
TEST(SourceText, ConstraintDeclDynamicOverride) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint :initial c1 { x > 0; }\n"
      "  constraint :extends c2 { x < 100; }\n"
      "  constraint :final c3 { x == 42; }\n"
      "  constraint :initial :final c4 { x != 0; }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_GE(members.size(), 5u);
  EXPECT_EQ(members[1]->name, "c1");
  EXPECT_EQ(members[2]->name, "c2");
  EXPECT_EQ(members[3]->name, "c3");
  EXPECT_EQ(members[4]->name, "c4");
}

}  // namespace
