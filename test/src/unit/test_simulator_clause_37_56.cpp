#include <gtest/gtest.h>

#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.56 multiclock sequence expression: the VPI object model for a multiclock
// sequence expression. The diagram draws a multiclock sequence expression built
// from one-to-many clocked seq members (a double, tagless arrow), and each
// clocked seq pairing a clocking event (a one-to-one vpiClockingEvent -> expr
// edge) with a sequence expression (a one-to-one, tagless -> sequence expr
// edge). These tests observe the production helpers in vpi.cpp that apply those
// relations.

// Diagram (multiclock sequence expr ==> clocked seq): the one-to-many
// vpiClockedSeq iteration returns the multiclock sequence expression's
// clocked-seq members, in order, and reports none for a null handle.
TEST(MulticlockSequenceExprModel, ClockedSeqsCollectClockedSeqMembersInOrder) {
  VpiObject multiclock;
  multiclock.type = vpiMulticlockSequenceExpr;
  VpiObject first;
  first.type = vpiClockedSeq;
  VpiObject second;
  second.type = vpiClockedSeq;
  multiclock.children = {&first, &second};

  auto seqs = VpiMulticlockSequenceClockedSeqs(&multiclock);
  ASSERT_EQ(seqs.size(), 2u);
  EXPECT_EQ(seqs[0], &first);
  EXPECT_EQ(seqs[1], &second);

  EXPECT_TRUE(VpiMulticlockSequenceClockedSeqs(nullptr).empty());
}

// Diagram (multiclock sequence expr ==> clocked seq): the relation matches by
// the clocked-seq kind, so children that are not clocked sequences are skipped
// while the clocked-seq members keep their relative order.
TEST(MulticlockSequenceExprModel, ClockedSeqsSkipNonClockedSeqChildren) {
  VpiObject multiclock;
  multiclock.type = vpiMulticlockSequenceExpr;
  VpiObject ev;
  ev.type = vpiEventControl;
  VpiObject seq;
  seq.type = vpiClockedSeq;
  VpiObject other;
  other.type = vpiOperation;
  multiclock.children = {&ev, &seq, &other};

  auto seqs = VpiMulticlockSequenceClockedSeqs(&multiclock);
  ASSERT_EQ(seqs.size(), 1u);
  EXPECT_EQ(seqs[0], &seq);
}

// Diagram (clocked seq -- vpiClockingEvent --> expr): a clocked seq traverses
// to its clocking event through the same one-to-one relation a property spec
// and a clocked property use, modeled as its event-control child; none when no
// clocking event is attached.
TEST(MulticlockSequenceExprModel, ClockedSeqReachesItsClockingEvent) {
  VpiObject clocked;
  clocked.type = vpiClockedSeq;
  VpiObject ev;
  ev.type = vpiEventControl;
  clocked.children = {&ev};
  EXPECT_EQ(VpiClockingEvent(&clocked), &ev);

  VpiObject unclocked;
  unclocked.type = vpiClockedSeq;
  EXPECT_EQ(VpiClockingEvent(&unclocked), nullptr);
}

// Diagram (clocked seq -> sequence expr): the one-to-one, tagless edge reaches
// the clocked seq's sequence-expr-kind child (the §37.54 sequence-expr class);
// none when no sequence expression is attached.
TEST(MulticlockSequenceExprModel, ClockedSeqReachesItsSequenceExpr) {
  VpiObject clocked;
  clocked.type = vpiClockedSeq;
  VpiObject seq_expr;
  seq_expr.type = vpiOperation;  // a sequence-expr kind
  clocked.children = {&seq_expr};
  EXPECT_EQ(VpiClockedSeqSequenceExpr(&clocked), &seq_expr);

  VpiObject empty;
  empty.type = vpiClockedSeq;
  EXPECT_EQ(VpiClockedSeqSequenceExpr(&empty), nullptr);
  EXPECT_EQ(VpiClockedSeqSequenceExpr(nullptr), nullptr);

  // The edge is one-to-one (a single arrow): a clocked seq clocks exactly one
  // sequence expression, so the relation yields a single handle - the first
  // sequence-expr-kind child - rather than enumerating several.
  VpiObject paired;
  paired.type = vpiClockedSeq;
  VpiObject primary;
  primary.type = vpiOperation;
  VpiObject later;
  later.type = vpiSequenceInst;
  paired.children = {&primary, &later};
  EXPECT_EQ(VpiClockedSeqSequenceExpr(&paired), &primary);
}

// Diagram (clocked seq's two edges are distinct): when a clocked seq carries
// both a clocking event and a sequence expression, the vpiClockingEvent edge
// and the sequence-expr edge resolve to the two different objects - the
// event-control child is not mistaken for the sequence expression, nor the
// reverse.
TEST(MulticlockSequenceExprModel,
     ClockingEventAndSequenceExprAreDistinctEdges) {
  VpiObject clocked;
  clocked.type = vpiClockedSeq;
  VpiObject ev;
  ev.type = vpiEventControl;
  VpiObject seq_expr;
  seq_expr.type = vpiSequenceInst;  // a sequence-expr kind
  clocked.children = {&ev, &seq_expr};

  EXPECT_EQ(VpiClockingEvent(&clocked), &ev);
  EXPECT_EQ(VpiClockedSeqSequenceExpr(&clocked), &seq_expr);
}

// Diagram (multiclock sequence expr ==> clocked seq) through the public VPI
// path: vpi_iterate(vpiClockedSeq, multiclockHandle) walks the multiclock
// sequence expression's clocked-seq members. The dispatch collects exactly the
// clocked-seq children, in order, skipping unrelated children, then drains and
// frees the iterator.
TEST(MulticlockSequenceExprModel, IterateClockedSeqsThroughVpiDispatch) {
  VpiContext ctx;
  VpiObject multiclock;
  multiclock.type = vpiMulticlockSequenceExpr;
  VpiObject first;
  first.type = vpiClockedSeq;
  VpiObject other;
  other.type = vpiOperation;  // not a clocked seq
  VpiObject second;
  second.type = vpiClockedSeq;
  multiclock.children = {&first, &other, &second};

  VpiHandle it = ctx.Iterate(vpiClockedSeq, &multiclock);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(ctx.Scan(it), &first);
  EXPECT_EQ(ctx.Scan(it), &second);
  EXPECT_EQ(ctx.Scan(it), nullptr);  // drains and frees the iterator
}

// Diagram edge: a multiclock sequence expression with no clocked-seq members
// yields no iterator at all, matching the empty one-to-many relation.
TEST(MulticlockSequenceExprModel, IterateClockedSeqsEmptyWhenNonePresent) {
  VpiContext ctx;
  VpiObject multiclock;
  multiclock.type = vpiMulticlockSequenceExpr;
  VpiObject lone;
  lone.type = vpiEventControl;  // present, but not a clocked seq
  multiclock.children = {&lone};

  EXPECT_EQ(ctx.Iterate(vpiClockedSeq, &multiclock), nullptr);
}

}  // namespace
}  // namespace delta
