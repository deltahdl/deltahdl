// §11.11 gives a min:typ:max expression three values and says "the three
// values allow a design to be tested with minimum, typical, or maximum delay
// values", so which of the three a constant expression folds to is one setting
// for a whole elaboration. DelayModeGuard in src/elaborator/const_eval.h
// installs that setting and ActiveDelayMode answers it; these cases are over
// what ConstEvalFull in src/elaborator/const_eval_func.cpp does with it.
//
// The design each case elaborates writes the triple in parentheses, which
// A.8.4 admits as `constant_primary ::= ( constant_mintypmax_expression )` and
// Parser::ParseParenExpr in src/parser/expr_parser_aux.cpp builds into an
// ExprKind::kMinTypMax with the three members in Expr::lhs, Expr::condition and
// Expr::rhs.
//
// The triple is 11:22:33 so that no member coincides with another, with its
// position among the three, or with the 0 a fold that gave up leaves in
// RtlirParamDecl::resolved_value. A triple of 0:1:2 would let a folder that
// returned the position it selected, or one that folded nothing at all, answer
// a case that asked for the minimum.

#include <cstdint>

#include "common/types.h"
#include "elaborator/const_eval.h"
#include "fixture_elaborator.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

// Elaborates the one design these cases share and answers what its parameter
// folded to, so that each case states only which mode was installed and which
// member came back.
int64_t FoldedTripleParam(ElabFixture& f) {
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int P = (11:22:33);\n"
      "endmodule\n",
      f);
  if (design == nullptr) {
    ADD_FAILURE() << "the source did not elaborate, so nothing folded";
    return 0;
  }
  EXPECT_FALSE(f.has_errors);
  const auto* p = FindParam(design, "m", "P");
  if (p == nullptr) {
    ADD_FAILURE() << "the elaborated design declares no parameter P";
    return 0;
  }
  return p->resolved_value;
}

// §11.11 orders the three "minimum, typical, and maximum values -- in that
// order", and the typical member is what the folder takes when nothing has
// asked for another. This is what a run given no --mintypmax gets.
TEST(MinTypMaxElaboration, TypicalMemberFoldsWhenNoDelayModeGuardIsLive) {
  ElabFixture f;
  EXPECT_EQ(FoldedTripleParam(f), 22);
}

// The minimum member, which §11.11's "tested with minimum ... delay values" is
// about. Nothing but the live guard differs from the case above.
TEST(MinTypMaxElaboration, MinimumMemberFoldsWhileAMinimumGuardIsLive) {
  ElabFixture f;
  DelayModeGuard guard(DelayMode::kMin);
  EXPECT_EQ(FoldedTripleParam(f), 11);
}

// The maximum member, the third of the three §11.11 names.
TEST(MinTypMaxElaboration, MaximumMemberFoldsWhileAMaximumGuardIsLive) {
  ElabFixture f;
  DelayModeGuard guard(DelayMode::kMax);
  EXPECT_EQ(FoldedTripleParam(f), 33);
}

// The guard restores the mode it found rather than writing the default back, so
// one elaboration cannot leak its mode into the next.
//
// The outer guard names the maximum on purpose. A destructor that assigned
// DelayMode::kTyp instead of the mode it saved would satisfy a case whose outer
// mode was already the typical one, because the two answers coincide there.
// Here such a destructor folds 22 where 33 is required.
TEST(MinTypMaxElaboration, AGuardRestoresTheModeItFoundRatherThanTheDefault) {
  DelayModeGuard outer(DelayMode::kMax);
  {
    ElabFixture under_inner;
    DelayModeGuard inner(DelayMode::kMin);
    EXPECT_EQ(FoldedTripleParam(under_inner), 11);
  }
  EXPECT_EQ(ActiveDelayMode(), DelayMode::kMax);
  ElabFixture after_inner;
  EXPECT_EQ(FoldedTripleParam(after_inner), 33);
}

}  // namespace
