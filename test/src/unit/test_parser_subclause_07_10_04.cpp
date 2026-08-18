#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §7.10.4 writes seven of its nine assignment forms with a queue slice or an
// unpacked array concatenation on the right. Each test below states one of
// those forms as source and reads back the shape the parser built for it,
// because the simulator recognizes a form by that shape: a slice is a select
// carrying a second bound, and a concatenation is a list of items whose slices
// are held verbatim.

// §7.10.4: `q = { q, 6 }` parses as an unpacked array concatenation of two
// items, the queue and the value appended to it.
TEST(QueueAssignParsing, ConcatAppendHasTwoItems) {
  auto r = Parse(
      "module m;\n"
      "  int q[$];\n"
      "  initial q = {q, 6};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kConcatenation);
  ASSERT_EQ(rhs->elements.size(), 2u);
  EXPECT_EQ(rhs->elements[0]->text, "q");
}

// §7.10.4: `q = { e, q }` parses with the items in the order written, which is
// what makes it a push_front rather than a push_back.
TEST(QueueAssignParsing, ConcatPrependKeepsItemOrder) {
  auto r = Parse(
      "module m;\n"
      "  int q[$];\n"
      "  int e;\n"
      "  initial q = {e, q};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  ASSERT_EQ(rhs->elements.size(), 2u);
  EXPECT_EQ(rhs->elements[0]->text, "e");
}

// §7.10.4: `q = q[1:$]` parses as a select carrying both bounds. A select with
// no second bound names one element, so the second bound is what separates a
// slice from an element read.
TEST(QueueAssignParsing, BareSliceCarriesBothBounds) {
  auto r = Parse(
      "module m;\n"
      "  int q[$];\n"
      "  initial q = q[1:$];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_NE(rhs->index_end, nullptr);
}

// §7.10.1: `$` in a slice bound names the queue's last index. It parses as an
// identifier-shaped node whose text is `$`, which is the name the simulator
// binds that index to.
TEST(QueueAssignParsing, DollarBoundIsNamedDollar) {
  auto r = Parse(
      "module m;\n"
      "  int q[$];\n"
      "  initial q = q[1:$];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  ASSERT_NE(rhs->index_end, nullptr);
  EXPECT_EQ(rhs->index_end->text, "$");
}

// §7.10.4: the upper bound of `q = q[0:$-1]` is an expression over `$` rather
// than a bare bound, which §7.10.1 allows by saying the slice bounds "may be
// arbitrary integral expressions".
TEST(QueueAssignParsing, DollarMinusOneBoundIsBinary) {
  auto r = Parse(
      "module m;\n"
      "  int q[$];\n"
      "  initial q = q[0:$-1];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  ASSERT_NE(rhs->index_end, nullptr);
  EXPECT_EQ(rhs->index_end->kind, ExprKind::kBinary);
}

// §7.10.4: a slice written as an item of `q = { q[0:pos-1], e, q[pos:$] }` is
// held as a select, not folded into the concatenation. Folding it would lose
// the run of elements it names.
TEST(QueueAssignParsing, SliceInsideBracesStaysASelect) {
  auto r = Parse(
      "module m;\n"
      "  int q[$];\n"
      "  int e, pos;\n"
      "  initial q = {q[0:pos-1], e, q[pos:$]};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  ASSERT_EQ(rhs->elements.size(), 3u);
  EXPECT_EQ(rhs->elements[0]->kind, ExprKind::kSelect);
}

// §7.10: `q = {}` is the empty queue, written as a concatenation with no items.
TEST(QueueAssignParsing, EmptyConcatHasNoItems) {
  auto r = Parse(
      "module m;\n"
      "  int q[$];\n"
      "  initial q = {};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_TRUE(rhs->elements.empty());
}

// §7.10.4 with §10.4.2: the nonblocking spelling parses to the same right-hand
// side, so the simulator sees one shape whichever assignment operator was
// written.
TEST(QueueAssignParsing, NonblockingBareSliceCarriesBothBounds) {
  auto r = Parse(
      "module m;\n"
      "  int q[$];\n"
      "  initial q <= q[1:$];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_NE(stmt->rhs->index_end, nullptr);
}

}  // namespace
