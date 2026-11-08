#include <gtest/gtest.h>

#include <string_view>
#include <vector>

#include "fixture_parser.h"
#include "parser/ast_class.h"

using namespace delta;

namespace {

TEST(SolveBeforeOrdering, SingleVariableEachSideAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand bit s;\n"
      "  rand bit [31:0] d;\n"
      "  constraint c { s -> d == 0; solve s before d; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(SolveBeforeOrdering, MultipleVariableListsAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int a, b, c, d;\n"
      "  constraint k { solve a, b before c, d; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(SolveBeforeOrdering, ArraySizeMethodAcceptedParses) {
  auto r = Parse(
      "class C;\n"
      "  rand int A[];\n"
      "  rand int n;\n"
      "  constraint k { solve A.size() before n; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(SolveBeforeOrdering, ImplicitClassHandleQualifierAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  rand int y;\n"
      "  constraint k { solve this.x before this.y; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(SolveBeforeOrdering, MixedValueAndOrderingConstraintsAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand bit s;\n"
      "  rand bit [7:0] d;\n"
      "  constraint c {\n"
      "    d inside {[0:200]};\n"
      "    s -> d == 0;\n"
      "    solve s before d;\n"
      "  }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(SolveBeforeOrdering, ChainedOrderingStatementsAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int a, b, c;\n"
      "  constraint k { solve a before b; solve b before c; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(SolveBeforeOrdering, ClassScopeQualifierAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  rand int y;\n"
      "  constraint k { solve C::x before y; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(SolveBeforeOrdering, IndexedSelectPrimaryAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int q[4];\n"
      "  rand int n;\n"
      "  constraint k { solve q[0] before n; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(SolveBeforeOrdering, ADottedPrimaryKeepsItsHandles) {
  auto r = Parse(
      "class C;\n"
      "  rand int q[4];\n"
      "  rand int n;\n"
      "  constraint k { solve l.m.v, C::n, q.size(), q[0] before n; }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  const ClassMember* block = nullptr;
  for (const ClassMember* m : r.cu->classes[0]->members)
    if (m->kind == ClassMemberKind::kConstraint) block = m;
  ASSERT_NE(block, nullptr);
  ASSERT_EQ(block->constraint_solve_before_refs.size(), 1U);
  const auto& before = block->constraint_solve_before_refs[0].before;
  ASSERT_EQ(before.size(), 4U);
  EXPECT_EQ(before[0].name, "v");
  EXPECT_EQ(before[0].handles, (std::vector<std::string_view>{"l", "m"}));
  EXPECT_TRUE(before[1].handles.empty());
  EXPECT_TRUE(before[2].handles.empty());
  EXPECT_TRUE(before[3].handles.empty());
}

}  // namespace
