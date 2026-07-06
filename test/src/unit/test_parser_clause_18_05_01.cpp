#include "fixture_parser.h"

using namespace delta;

namespace {

// Locate a constraint member of the given name within a parsed class.
const ClassMember* FindConstraint(const ClassDecl* cls, std::string_view name) {
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kConstraint && m->name == name) return m;
  }
  return nullptr;
}

// 18.5.1: a constraint prototype may take an implicit form, written as a
// constraint declaration with a name but no block. The parser records such a
// member as a prototype that does not use the 'extern' keyword.
TEST(ExternalConstraintBlockParsing, ImplicitPrototypeFormRecognized) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint proto1;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->classes.empty());
  const auto* m = FindConstraint(r.cu->classes.front(), "proto1");
  ASSERT_NE(m, nullptr);
  EXPECT_TRUE(m->is_constraint_prototype);
  EXPECT_FALSE(m->is_constraint_extern);
}

// 18.5.1: the explicit prototype form uses the 'extern' keyword before the
// named, bodyless constraint declaration. The parser marks it both as a
// prototype and as the extern form.
TEST(ExternalConstraintBlockParsing, ExplicitPrototypeFormRecognized) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  extern constraint proto2;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->classes.empty());
  const auto* m = FindConstraint(r.cu->classes.front(), "proto2");
  ASSERT_NE(m, nullptr);
  EXPECT_TRUE(m->is_constraint_prototype);
  EXPECT_TRUE(m->is_constraint_extern);
}

// 18.5.1: a prototype is distinguished from an ordinary in-class constraint by
// the absence of a block. A constraint that carries a block is not a prototype.
TEST(ExternalConstraintBlockParsing, ConstraintWithBodyIsNotPrototype) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x > 0; }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->classes.empty());
  const auto* m = FindConstraint(r.cu->classes.front(), "c");
  ASSERT_NE(m, nullptr);
  EXPECT_FALSE(m->is_constraint_prototype);
}

// 18.5.1: a prototype is completed by an external constraint block declared
// outside the class using the class scope resolution operator. The parser
// records the block's owning class and constraint name from 'C::proto2'.
TEST(ExternalConstraintBlockParsing, ExternalBlockRecordsClassAndName) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  extern constraint proto2;\n"
      "endclass\n"
      "constraint C::proto2 { x >= 0; }\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->external_constraints.size(), 1u);
  EXPECT_EQ(r.cu->external_constraints.front().class_name, "C");
  EXPECT_EQ(r.cu->external_constraints.front().constraint_name, "proto2");
}

// 18.5.1: an external constraint block completes the prototype with the
// relations in its body. The parser captures each top-level relation so that
// elaboration can attach them to the prototype; a block with two relations
// records two, not the discarded body of before.
TEST(ExternalConstraintBlockParsing, ExternalBlockCapturesBodyRelations) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  extern constraint proto2;\n"
      "endclass\n"
      "constraint C::proto2 { x >= 0; x < 10; }\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->external_constraints.size(), 1u);
  EXPECT_EQ(r.cu->external_constraints.front().constraint_exprs.size(), 2u);
}

}  // namespace
