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

TEST(MulticlockSequenceExprModel, ClockedSeqReachesItsSequenceExpr) {
  VpiObject clocked;
  clocked.type = vpiClockedSeq;
  VpiObject seq_expr;
  seq_expr.type = vpiOperation;
  clocked.children = {&seq_expr};
  EXPECT_EQ(VpiClockedSeqSequenceExpr(&clocked), &seq_expr);

  VpiObject empty;
  empty.type = vpiClockedSeq;
  EXPECT_EQ(VpiClockedSeqSequenceExpr(&empty), nullptr);
  EXPECT_EQ(VpiClockedSeqSequenceExpr(nullptr), nullptr);

  VpiObject paired;
  paired.type = vpiClockedSeq;
  VpiObject primary;
  primary.type = vpiOperation;
  VpiObject later;
  later.type = vpiSequenceInst;
  paired.children = {&primary, &later};
  EXPECT_EQ(VpiClockedSeqSequenceExpr(&paired), &primary);
}

TEST(MulticlockSequenceExprModel, ClockedSeqSequenceExprAcceptsDistribution) {
  VpiObject clocked;
  clocked.type = vpiClockedSeq;
  VpiObject dist;
  dist.type = vpiDistribution;
  clocked.children = {&dist};
  EXPECT_EQ(VpiClockedSeqSequenceExpr(&clocked), &dist);
}

TEST(MulticlockSequenceExprModel, ClockedSeqSequenceExprAcceptsConstantExpr) {
  VpiObject clocked;
  clocked.type = vpiClockedSeq;
  VpiObject constant;
  constant.type = vpiConstant;
  clocked.children = {&constant};
  EXPECT_EQ(VpiClockedSeqSequenceExpr(&clocked), &constant);
}

TEST(MulticlockSequenceExprModel, ClockedSeqSequenceExprAcceptsReference) {
  VpiObject clocked;
  clocked.type = vpiClockedSeq;
  VpiObject ref;
  ref.type = vpiRefObj;
  clocked.children = {&ref};
  EXPECT_EQ(VpiClockedSeqSequenceExpr(&clocked), &ref);
}

TEST(MulticlockSequenceExprModel,
     ClockedSeqSequenceExprRejectsNonSequenceChild) {
  VpiObject clocked;
  clocked.type = vpiClockedSeq;
  VpiObject ev;
  ev.type = vpiEventControl;
  clocked.children = {&ev};
  EXPECT_EQ(VpiClockedSeqSequenceExpr(&clocked), nullptr);
}

TEST(MulticlockSequenceExprModel, IterateClockedSeqsThroughVpiDispatch) {
  VpiContext ctx;
  VpiObject multiclock;
  multiclock.type = vpiMulticlockSequenceExpr;
  VpiObject first;
  first.type = vpiClockedSeq;
  VpiObject other;
  other.type = vpiOperation;
  VpiObject second;
  second.type = vpiClockedSeq;
  multiclock.children = {&first, &other, &second};

  VpiHandle it = ctx.Iterate(vpiClockedSeq, &multiclock);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(ctx.Scan(it), &first);
  EXPECT_EQ(ctx.Scan(it), &second);
  EXPECT_EQ(ctx.Scan(it), nullptr);
}

TEST(MulticlockSequenceExprModel, HandleClockingEventThroughVpiDispatch) {
  VpiContext ctx;
  VpiObject clocked;
  clocked.type = vpiClockedSeq;
  VpiObject ev;
  ev.type = vpiEventControl;
  VpiObject seq_expr;
  seq_expr.type = vpiSequenceInst;
  clocked.children = {&ev, &seq_expr};

  EXPECT_EQ(ctx.Handle(vpiClockingEvent, &clocked), &ev);
}

TEST(MulticlockSequenceExprModel, HandleClockingEventNullWhenNoClockAttached) {
  VpiContext ctx;
  VpiObject clocked;
  clocked.type = vpiClockedSeq;
  VpiObject seq_expr;
  seq_expr.type = vpiOperation;
  clocked.children = {&seq_expr};

  EXPECT_EQ(ctx.Handle(vpiClockingEvent, &clocked), nullptr);
}

TEST(MulticlockSequenceExprModel, MulticlockTraversalResolvesPerClockedSeq) {
  VpiContext ctx;

  VpiObject clock_a;
  clock_a.type = vpiEventControl;
  VpiObject seq_a;
  seq_a.type = vpiOperation;
  VpiObject clocked_a;
  clocked_a.type = vpiClockedSeq;
  clocked_a.children = {&clock_a, &seq_a};

  VpiObject clock_b;
  clock_b.type = vpiEventControl;
  VpiObject seq_b;
  seq_b.type = vpiSequenceInst;
  VpiObject clocked_b;
  clocked_b.type = vpiClockedSeq;
  clocked_b.children = {&clock_b, &seq_b};

  VpiObject multiclock;
  multiclock.type = vpiMulticlockSequenceExpr;
  multiclock.children = {&clocked_a, &clocked_b};

  VpiHandle it = ctx.Iterate(vpiClockedSeq, &multiclock);
  ASSERT_NE(it, nullptr);
  VpiHandle m0 = ctx.Scan(it);
  VpiHandle m1 = ctx.Scan(it);
  EXPECT_EQ(ctx.Scan(it), nullptr);
  ASSERT_EQ(m0, &clocked_a);
  ASSERT_EQ(m1, &clocked_b);

  EXPECT_EQ(ctx.Handle(vpiClockingEvent, m0), &clock_a);
  EXPECT_EQ(VpiClockedSeqSequenceExpr(m0), &seq_a);
  EXPECT_EQ(ctx.Handle(vpiClockingEvent, m1), &clock_b);
  EXPECT_EQ(VpiClockedSeqSequenceExpr(m1), &seq_b);
}

TEST(MulticlockSequenceExprModel, IterateClockedSeqsEmptyWhenNonePresent) {
  VpiContext ctx;
  VpiObject multiclock;
  multiclock.type = vpiMulticlockSequenceExpr;
  VpiObject lone;
  lone.type = vpiEventControl;
  multiclock.children = {&lone};

  EXPECT_EQ(ctx.Iterate(vpiClockedSeq, &multiclock), nullptr);
}

class MulticlockSequencesOfARun : public VpiDesignRun {
 protected:
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
