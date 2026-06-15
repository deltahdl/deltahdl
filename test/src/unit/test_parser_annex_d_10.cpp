#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// Annex D.10: $scale is a system function whose single argument is a
// hierarchical name. It parses as an ordinary system call with that name as its
// lone argument.
TEST(OptionalScaleParser, ScaleParsesAsSystemCall) {
  auto r = Parse(
      "module m;\n"
      "  initial x = $scale(top.d);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* call = r.cu->modules[0]->items[0]->body->rhs;
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(call->kind, ExprKind::kSystemCall);
  EXPECT_EQ(call->callee, "$scale");
  ASSERT_EQ(call->args.size(), 1u);
  EXPECT_EQ(call->args[0]->kind, ExprKind::kMemberAccess);
}

// Annex D.10 (edge case): a hierarchical name may be a single, unqualified
// identifier. The argument then parses as a plain identifier rather than a
// member-access chain, but $scale still parses as an ordinary system call.
TEST(OptionalScaleParser, ScaleAcceptsSimpleName) {
  auto r = Parse(
      "module m;\n"
      "  initial x = $scale(d);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* call = r.cu->modules[0]->items[0]->body->rhs;
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(call->kind, ExprKind::kSystemCall);
  EXPECT_EQ(call->callee, "$scale");
  ASSERT_EQ(call->args.size(), 1u);
  EXPECT_EQ(call->args[0]->kind, ExprKind::kIdentifier);
}

}
