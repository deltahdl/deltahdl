// §18.5.1: External constraint blocks

#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

namespace {

// package_or_generate_item_declaration: extern_constraint_declaration
TEST(SourceText, PackageItemExternConstraint) {
  auto r = Parse(
      "package pkg;\n"
      "  constraint MyClass::c { x > 0; }\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

using CheckerParseTest = ProgramTestParse;

// constraint_prototype ::=
//   [constraint_prototype_qualifier] [static] constraint
//   [dynamic_override_specifiers] constraint_identifier ;
// constraint_prototype_qualifier ::= extern | pure
TEST(SourceText, ConstraintPrototype) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  extern constraint c1;\n"
      "  pure constraint c2;\n"
      "  extern static constraint c3;\n"
      "  constraint c4;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_GE(members.size(), 5u);
  EXPECT_EQ(members[1]->kind, ClassMemberKind::kConstraint);
  EXPECT_EQ(members[1]->name, "c1");
  EXPECT_EQ(members[2]->name, "c2");
  EXPECT_EQ(members[3]->name, "c3");
  EXPECT_TRUE(members[3]->is_static);
  EXPECT_EQ(members[4]->name, "c4");
}

}  // namespace
