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

// 18.5.13 / Syntax 18-2: a soft constraint is the inner expression_or_dist
// preceded by 'soft'. The parser captures that inner relation apart from the
// hard relations so the simulator can build it as a discardable soft solver
// constraint. Here the only relation is soft, so the constraint member carries
// exactly one soft relation and no hard one — observing that the 'soft' prefix
// routes the relation to the soft list rather than dropping it (as it was
// before) or filing it as a hard constraint.
TEST(SoftConstraintParsing, SoftRelationCapturedAsSoftNotHard) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { soft x == 42; }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->classes.empty());
  const auto* m = FindConstraint(r.cu->classes.front(), "c");
  ASSERT_NE(m, nullptr);
  EXPECT_EQ(m->constraint_soft_exprs.size(), 1u);
  EXPECT_TRUE(m->constraint_exprs.empty());
}

// 18.5.13: a constraint block may mix hard and soft relations. The parser must
// keep them apart: the hard relation goes to the ordinary relation list and the
// soft one to the soft list. A block with one of each therefore yields exactly
// one entry in each, so the 'soft' prefix distinguishes the two rather than
// bleeding a soft preference into the always-satisfied hard set.
TEST(SoftConstraintParsing, HardAndSoftInSameBlockSeparated) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x > 0; soft x == 5; }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->classes.empty());
  const auto* m = FindConstraint(r.cu->classes.front(), "c");
  ASSERT_NE(m, nullptr);
  EXPECT_EQ(m->constraint_exprs.size(), 1u);
  EXPECT_EQ(m->constraint_soft_exprs.size(), 1u);
}

}  // namespace
