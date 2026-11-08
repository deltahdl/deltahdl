#include <gtest/gtest.h>

#include <string_view>

#include "fixture_parser.h"
#include "parser/ast_class.h"

using namespace delta;

namespace {

const ClassMember* FindConstraint(const ClassDecl* cls, std::string_view name) {
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kConstraint && m->name == name) return m;
  }
  return nullptr;
}

bool RefersTo(const ClassMember* m, std::string_view callee) {
  for (const auto& r : m->constraint_function_call_refs) {
    if (r.callee == callee) return true;
  }
  return false;
}

TEST(FunctionsInConstraintsParsing, RecordsUnqualifiedCall) {
  auto r = Parse(
      "class C;\n"
      "  rand bit [9:0] v;\n"
      "  rand int length;\n"
      "  function int count_ones(bit [9:0] w); return 0; endfunction\n"
      "  constraint c1 { length == count_ones(v); }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->classes.empty());
  const auto* m = FindConstraint(r.cu->classes.front(), "c1");
  ASSERT_NE(m, nullptr);
  EXPECT_TRUE(RefersTo(m, "count_ones"));
}

TEST(FunctionsInConstraintsParsing, NoCallRecordsNothing) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c1 { x > 0; }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  const auto* m = FindConstraint(r.cu->classes.front(), "c1");
  ASSERT_NE(m, nullptr);
  EXPECT_TRUE(m->constraint_function_call_refs.empty());
}

TEST(FunctionsInConstraintsParsing, MemberQualifiedCallNotRecorded) {
  auto r = Parse(
      "class D; endclass\n"
      "class C;\n"
      "  rand int x;\n"
      "  D d;\n"
      "  constraint c1 { x == d.f(); }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  const auto* m = FindConstraint(r.cu->classes.back(), "c1");
  ASSERT_NE(m, nullptr);
  EXPECT_FALSE(RefersTo(m, "f"));
}

TEST(FunctionsInConstraintsParsing, ScopeQualifiedCallNotRecorded) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c1 { x == pkg::f(x); }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  const auto* m = FindConstraint(r.cu->classes.front(), "c1");
  ASSERT_NE(m, nullptr);
  EXPECT_FALSE(RefersTo(m, "f"));
}

TEST(FunctionsInConstraintsParsing, RecordsMultipleCalls) {
  auto r = Parse(
      "class C;\n"
      "  rand int x, y;\n"
      "  function int f(int a); return a; endfunction\n"
      "  function int g(int a); return a; endfunction\n"
      "  constraint c1 { x == f(y); y == g(x); }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  const auto* m = FindConstraint(r.cu->classes.front(), "c1");
  ASSERT_NE(m, nullptr);
  EXPECT_TRUE(RefersTo(m, "f"));
  EXPECT_TRUE(RefersTo(m, "g"));
}

TEST(FunctionsInConstraintsParsing, RecordsNestedCall) {
  auto r = Parse(
      "class C;\n"
      "  rand int x, y;\n"
      "  function int f(int a); return a; endfunction\n"
      "  function int g(int a); return a; endfunction\n"
      "  constraint c1 { x == f(g(y)); }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  const auto* m = FindConstraint(r.cu->classes.front(), "c1");
  ASSERT_NE(m, nullptr);
  EXPECT_TRUE(RefersTo(m, "f"));
  EXPECT_TRUE(RefersTo(m, "g"));
}

}  // namespace
