#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_class.h"

using namespace delta;

namespace {

const ClassMember* FindConstraint(const ClassDecl* cls, std::string_view name) {
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kConstraint && m->name == name) return m;
  }
  return nullptr;
}

TEST(ConstraintInheritanceParsing, InitialAndExtendsRejected) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint :initial :extends c { x > 0; }\n"
      "endclass\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got 'extends'", 3, "18.5"));
}

TEST(ConstraintInheritanceParsing, InitialFinalCombinationRecorded) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint :initial :final c { x > 0; }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->classes.empty());
  const auto* m = FindConstraint(r.cu->classes.front(), "c");
  ASSERT_NE(m, nullptr);
  EXPECT_TRUE(m->is_constraint_initial);
  EXPECT_TRUE(m->is_constraint_final);
}

TEST(ConstraintInheritanceParsing, ExtendsFinalCombinationRecorded) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint :extends :final c { x > 0; }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->classes.empty());
  const auto* m = FindConstraint(r.cu->classes.front(), "c");
  ASSERT_NE(m, nullptr);
  EXPECT_TRUE(m->is_constraint_extends);
  EXPECT_TRUE(m->is_constraint_final);
}

void ExpectBothSpecifiersRejected(const std::string& member, int line,
                                  std::string_view message,
                                  const char* subclause = "18.5") {
  auto r = Parse(
      "class B;\n  rand int x;\n  constraint c { x > 0; }\nendclass\n"
      "virtual class C extends B;\n" +
      member +
      "endclass\n"
      "constraint :initial :extends C::k { x > 0; }\n");
  EXPECT_TRUE(ReportedError(r.diags, message, line, subclause)) << member;
}

TEST(ConstraintInheritanceParsing, ExtendsBeforeInitialOnABlockRejected) {
  ExpectBothSpecifiersRejected("  constraint :extends :initial c { x > 1; }\n",
                               6, "expected identifier, got 'initial'");
}

TEST(ConstraintInheritanceParsing, InitialExtendsOnAPrototypeRejected) {
  ExpectBothSpecifiersRejected("  constraint :initial :extends c;\n", 6,
                               "expected identifier, got 'extends'");
}

TEST(ConstraintInheritanceParsing, ExtendsInitialOnAnExternPrototypeRejected) {
  ExpectBothSpecifiersRejected("  extern constraint :extends :initial c;\n", 6,
                               "expected identifier, got 'initial'");
}

TEST(ConstraintInheritanceParsing, InitialExtendsOnAPureConstraintRejected) {
  ExpectBothSpecifiersRejected("  pure constraint :initial :extends c;\n", 6,
                               "expected identifier, got 'extends'");
}

TEST(ConstraintInheritanceParsing, InitialExtendsOnAnExternalBlockRejected) {
  ExpectBothSpecifiersRejected("  extern constraint k;\n", 8,
                               "expected identifier, got 'extends'", "18.5.1");
}

}  // namespace
