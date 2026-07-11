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

// Diagram (clocked seq -> sequence expr), input form: the sequence-expr target
// is drawn as the §37.54 sequence-expr class, whose members include a
// distribution. A clocked seq whose sequence expression is a distribution
// resolves through the same edge.
TEST(MulticlockSequenceExprModel, ClockedSeqSequenceExprAcceptsDistribution) {
  VpiObject clocked;
  clocked.type = vpiClockedSeq;
  VpiObject dist;
  dist.type = vpiDistribution;
  clocked.children = {&dist};
  EXPECT_EQ(VpiClockedSeqSequenceExpr(&clocked), &dist);
}

// Diagram (clocked seq -> sequence expr), input form: a bare boolean expression
// used directly as a sequence takes a concrete constant form. A clocked seq
// whose sequence expression is a constant resolves through the edge.
TEST(MulticlockSequenceExprModel, ClockedSeqSequenceExprAcceptsConstantExpr) {
  VpiObject clocked;
  clocked.type = vpiClockedSeq;
  VpiObject constant;
  constant.type = vpiConstant;
  clocked.children = {&constant};
  EXPECT_EQ(VpiClockedSeqSequenceExpr(&clocked), &constant);
}

// Diagram (clocked seq -> sequence expr), input form: the other concrete form
// of a bare boolean expression is a reference. A clocked seq whose sequence
// expression is a reference object resolves through the edge.
TEST(MulticlockSequenceExprModel, ClockedSeqSequenceExprAcceptsReference) {
  VpiObject clocked;
  clocked.type = vpiClockedSeq;
  VpiObject ref;
  ref.type = vpiRefObj;
  clocked.children = {&ref};
  EXPECT_EQ(VpiClockedSeqSequenceExpr(&clocked), &ref);
}

// Diagram (clocked seq -> sequence expr), negative form: a child that is not a
// member of the sequence-expr class is rejected, so a clocked seq whose only
// child is a clocking event (an event control) exposes no sequence expression
// through the edge - the relation walks past the ineligible child and reports
// none rather than mistaking it for a sequence expression.
TEST(MulticlockSequenceExprModel,
     ClockedSeqSequenceExprRejectsNonSequenceChild) {
  VpiObject clocked;
  clocked.type = vpiClockedSeq;
  VpiObject ev;
  ev.type = vpiEventControl;  // a clocking event, not a sequence-expr kind
  clocked.children = {&ev};
  EXPECT_EQ(VpiClockedSeqSequenceExpr(&clocked), nullptr);
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

// Diagram (clocked seq -- vpiClockingEvent --> expr) through the public VPI
// path: vpi_handle(vpiClockingEvent, clockedSeqHandle) reaches the clocked
// seq's clocking event, so a client that has iterated to a clocked-seq member
// can obtain its clock. The dispatch resolves to the event-control child.
TEST(MulticlockSequenceExprModel, HandleClockingEventThroughVpiDispatch) {
  VpiContext ctx;
  VpiObject clocked;
  clocked.type = vpiClockedSeq;
  VpiObject ev;
  ev.type = vpiEventControl;
  VpiObject seq_expr;
  seq_expr.type = vpiSequenceInst;  // a sequence-expr kind, not the clock
  clocked.children = {&ev, &seq_expr};

  EXPECT_EQ(ctx.Handle(vpiClockingEvent, &clocked), &ev);
}

// Diagram edge (negative): a clocked seq with no clocking event attached yields
// null through the same public relation - the dispatch does not fall through to
// a sequence-expr or other child.
TEST(MulticlockSequenceExprModel, HandleClockingEventNullWhenNoClockAttached) {
  VpiContext ctx;
  VpiObject clocked;
  clocked.type = vpiClockedSeq;
  VpiObject seq_expr;
  seq_expr.type = vpiOperation;  // a sequence-expr kind
  clocked.children = {&seq_expr};

  EXPECT_EQ(ctx.Handle(vpiClockingEvent, &clocked), nullptr);
}

// Diagram (all three edges composed): a multiclock sequence expression built
// from two clocked seqs, each pairing its own clocking event with its own
// sequence expression. Walking the figure the way a VPI client does - iterate
// the clocked-seq members (edge A, public), then for each reach its clocking
// event (edge B, public) and its sequence expression (edge C) - resolves each
// clocked seq's relations to that seq's own children. The second member's clock
// and sequence expression differ from the first's, so the relations are held
// per clocked seq rather than shared across the multiclock expression.
TEST(MulticlockSequenceExprModel, MulticlockTraversalResolvesPerClockedSeq) {
  VpiContext ctx;

  VpiObject clock_a;
  clock_a.type = vpiEventControl;
  VpiObject seq_a;
  seq_a.type = vpiOperation;  // a sequence-expr kind
  VpiObject clocked_a;
  clocked_a.type = vpiClockedSeq;
  clocked_a.children = {&clock_a, &seq_a};

  VpiObject clock_b;
  clock_b.type = vpiEventControl;
  VpiObject seq_b;
  seq_b.type = vpiSequenceInst;  // a different sequence-expr kind
  VpiObject clocked_b;
  clocked_b.type = vpiClockedSeq;
  clocked_b.children = {&clock_b, &seq_b};

  VpiObject multiclock;
  multiclock.type = vpiMulticlockSequenceExpr;
  multiclock.children = {&clocked_a, &clocked_b};

  // Edge A (public): iterate the clocked-seq members in order.
  VpiHandle it = ctx.Iterate(vpiClockedSeq, &multiclock);
  ASSERT_NE(it, nullptr);
  VpiHandle m0 = ctx.Scan(it);
  VpiHandle m1 = ctx.Scan(it);
  EXPECT_EQ(ctx.Scan(it), nullptr);
  ASSERT_EQ(m0, &clocked_a);
  ASSERT_EQ(m1, &clocked_b);

  // Edge B (public) + edge C: each member resolves to its own clock and its own
  // sequence expression, and the two members do not cross over.
  EXPECT_EQ(ctx.Handle(vpiClockingEvent, m0), &clock_a);
  EXPECT_EQ(VpiClockedSeqSequenceExpr(m0), &seq_a);
  EXPECT_EQ(ctx.Handle(vpiClockingEvent, m1), &clock_b);
  EXPECT_EQ(VpiClockedSeqSequenceExpr(m1), &seq_b);
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
