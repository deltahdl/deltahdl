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

bool RefersTo(const ClassMember* m, std::string_view callee) {
  for (const auto& r : m->constraint_function_call_refs) {
    if (r.callee == callee) return true;
  }
  return false;
}

// 18.5.11: a constraint expression may call a function. The parser records the
// unqualified call so the elaborator can resolve the callee and check it.
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

// 18.5.11: a constraint with no function call records none.
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

// 18.5.11: a member-qualified call (obj.f(...)) is not an unqualified call on the
// enclosing class, so its leaf name is not recorded as a constraint function
// call — only the receiver-free form is the function-in-constraint the clause
// governs.
TEST(FunctionsInConstraintsParsing, MemberQualifiedCallNotRecorded) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  D d;\n"
      "  constraint c1 { x == d.f(); }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  const auto* m = FindConstraint(r.cu->classes.front(), "c1");
  ASSERT_NE(m, nullptr);
  EXPECT_FALSE(RefersTo(m, "f"));
}

// 18.5.11: a scope-qualified call (pkg::f(...)) is likewise not recorded as an
// unqualified constraint function call.
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

// 18.5.11: every unqualified call in the body is recorded, so a constraint that
// calls more than one function lists each callee.
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

// 18.5.11: a call nested as the argument of another call is itself an unqualified
// call and is recorded too, so the restrictions can later be applied to both the
// outer and the inner function.
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
