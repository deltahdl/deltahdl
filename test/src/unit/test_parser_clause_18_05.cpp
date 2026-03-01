// §18.5: Constraint blocks

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserAnnexA, A2ClassWithConstraint) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c1 { x > 0; x < 100; }\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

using CheckerParseTest = ProgramTestParse;

// class_item ::= { attribute_instance } class_constraint
TEST(SourceText, ClassConstraint) {
  auto r = Parse(
      "class C;\n"
      "  int x;\n"
      "  constraint c1 { x > 0; }\n"
      "  constraint c2;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 3u);
  EXPECT_EQ(members[1]->kind, ClassMemberKind::kConstraint);
  EXPECT_EQ(members[1]->name, "c1");
  EXPECT_EQ(members[2]->kind, ClassMemberKind::kConstraint);
  EXPECT_EQ(members[2]->name, "c2");
}

}  // namespace
