#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

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

class MulticlockSequencesOfARun : public VpiDesignRun {
 protected:
  // The signal of the clocking event each clocked seq of `multiclock`
  // reaches, in order, empty for one reaching none.
  static std::vector<std::string> ClocksOf(vpiHandle multiclock) {
    std::vector<std::string> clocks;
    if (multiclock == nullptr) return clocks;
    vpiHandle it = vpi_iterate(vpiClockedSeq, multiclock);
    if (it == nullptr) return clocks;
    for (vpiHandle h = vpi_scan(it); h != nullptr; h = vpi_scan(it)) {
      const std::vector<vpiHandle> kEdge =
          OperandsOf(vpi_handle(vpiClockingEvent, h));
      const char* name =
          kEdge.size() == 1 ? vpi_get_str(vpiName, kEdge[0]) : nullptr;
      clocks.emplace_back(name == nullptr ? "" : name);
    }
    return clocks;
  }
};

// A sequence whose operands are evaluated on clocks of their own is a
// multiclock sequence expr, reaching a clocked seq per run of operands on one
// clock, the first on the clock flowing into it, each reaching its clock and
// its sequence expr (§16.13.1) (#5098).
TEST_F(MulticlockSequencesOfARun, AChainOnTwoClocksIsAMulticlockSequence) {
  Run("module top; logic clk1, clk2, a, b, c, d;\n"
      "  m1: assert property (@(posedge clk1) a ##1 b ##1 @(posedge clk2) c "
      "##2 d);\n"
      "endmodule\n");
  vpiHandle sequence = PropertyOf("m1");
  ASSERT_NE(sequence, nullptr);
  EXPECT_EQ(vpi_get(vpiType, sequence), vpiMulticlockSequenceExpr);
  std::vector<vpiHandle> clocked;
  vpiHandle it = vpi_iterate(vpiClockedSeq, sequence);
  ASSERT_NE(it, nullptr);
  for (vpiHandle h = vpi_scan(it); h != nullptr; h = vpi_scan(it)) {
    clocked.push_back(h);
  }
  ASSERT_EQ(clocked.size(), 2u);
  const char* const kNames[][2] = {{"a", "b"}, {"c", "d"}};
  const char* const kClocks[] = {"clk1", "clk2"};
  const int kDelays[] = {1, 2};
  for (size_t i = 0; i < clocked.size(); ++i) {
    vpiHandle event = vpi_handle(vpiClockingEvent, clocked[i]);
    ASSERT_NE(event, nullptr) << i;
    EXPECT_EQ(vpi_get(vpiOpType, event), vpiPosedgeOp) << i;
    const std::vector<vpiHandle> kEdge = OperandsOf(event);
    ASSERT_EQ(kEdge.size(), 1u) << i;
    EXPECT_STREQ(vpi_get_str(vpiName, kEdge[0]), kClocks[i]) << i;
    vpiHandle held = vpi_handle(vpiOperation, clocked[i]);
    ASSERT_NE(held, nullptr) << i;
    EXPECT_EQ(vpi_get(vpiOpType, held), vpiCycleDelayOp) << i;
    const std::vector<vpiHandle> kHeld = OperandsOf(held);
    ASSERT_EQ(kHeld.size(), 3u) << i;
    EXPECT_STREQ(vpi_get_str(vpiName, kHeld[0]), kNames[i][0]) << i;
    EXPECT_STREQ(vpi_get_str(vpiName, kHeld[1]), kNames[i][1]) << i;
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(kHeld[2], &value);
    EXPECT_EQ(value.value.integer, kDelays[i]) << i;
  }
}

// §16.13.3: the clock of a property spec flows into a sequence an
// implication's antecedent is, so the first clocked seq of a multiclock
// antecedent, naming no clock of its own, reaches the spec's clock (#5100).
TEST_F(MulticlockSequencesOfARun, AnAntecedentTakesTheClockFlowingIntoIt) {
  Run("module top; logic clk0, clk2, a, b, c;\n"
      "  m1: assert property (@(posedge clk0) (a ##1 @(posedge clk2) b) "
      "|-> c);\n"
      "endmodule\n");
  vpiHandle implication = PropertyOf("m1");
  ASSERT_NE(implication, nullptr);
  EXPECT_EQ(OpOf(implication), vpiOverlapImplyOp);
  const std::vector<vpiHandle> kOperands = OperandsOf(implication);
  ASSERT_EQ(kOperands.size(), 2u);
  EXPECT_EQ(vpi_get(vpiType, kOperands[0]), vpiMulticlockSequenceExpr);
  EXPECT_EQ(ClocksOf(kOperands[0]), (std::vector<std::string>{"clk0", "clk2"}));
}

// §16.13.3: the clock of a property spec flows across a not into the
// sequence it negates, the first clocked seq of a multiclock one reaching
// it (#5100).
TEST_F(MulticlockSequencesOfARun, ANegatedSequenceTakesTheClockFlowingIntoIt) {
  Run("module top; logic clk0, clk1, a, b;\n"
      "  m1: assert property (@(posedge clk0) not (a ##1 @(posedge clk1) "
      "b));\n"
      "endmodule\n");
  vpiHandle negation = PropertyOf("m1");
  ASSERT_NE(negation, nullptr);
  EXPECT_EQ(OpOf(negation), vpiNotOp);
  const std::vector<vpiHandle> kOperands = OperandsOf(negation);
  ASSERT_EQ(kOperands.size(), 1u);
  EXPECT_EQ(ClocksOf(kOperands[0]), (std::vector<std::string>{"clk0", "clk1"}));
}

// §16.13.3: the clock in force at the end of an antecedent flows into the
// consequent, so the first clocked seq of a multiclock consequent reaches
// the antecedent's last clock rather than the spec's (#5100).
TEST_F(MulticlockSequencesOfARun, AConsequentTakesTheAntecedentsEndClock) {
  Run("module top; logic clk0, clk1, clk2, a, b, c, d;\n"
      "  m1: assert property (@(posedge clk0) a ##1 @(posedge clk1) b |=> "
      "c ##1 @(posedge clk2) d);\n"
      "endmodule\n");
  vpiHandle implication = PropertyOf("m1");
  ASSERT_NE(implication, nullptr);
  EXPECT_EQ(OpOf(implication), vpiNonOverlapImplyOp);
  const std::vector<vpiHandle> kOperands = OperandsOf(implication);
  ASSERT_EQ(kOperands.size(), 2u);
  EXPECT_EQ(ClocksOf(kOperands[0]), (std::vector<std::string>{"clk0", "clk1"}));
  EXPECT_EQ(ClocksOf(kOperands[1]), (std::vector<std::string>{"clk1", "clk2"}));
}

// §37.56: a clocked seq's tagless edge is read with the type of the sequence
// expr it reaches, so a clocked seq holding none, or one of another type,
// resolves nothing for the type asked.
TEST(MulticlockSequenceExprModel, ClockedSeqEdgeNeedsAnExprOfTheTypeAsked) {
  VpiObject empty;
  empty.type = vpiClockedSeq;
  VpiHandle out = nullptr;
  EXPECT_FALSE(TryResolveProcessAndStmtRelation(vpiOperation, &empty, out));
  VpiObject seq_inst;
  seq_inst.type = vpiSequenceInst;
  VpiObject clocked;
  clocked.type = vpiClockedSeq;
  clocked.children = {&seq_inst};
  EXPECT_FALSE(TryResolveProcessAndStmtRelation(vpiOperation, &clocked, out));
  EXPECT_EQ(out, nullptr);
}
}  // namespace
}  // namespace delta
