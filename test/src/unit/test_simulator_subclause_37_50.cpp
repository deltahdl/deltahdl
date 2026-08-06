#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.50 concurrent assertion: the VPI object model for a concurrent assertion.
// The concurrent-assertion class is realized by the
// assert/assume/cover/restrict directives; a concurrent assertion traverses to
// its clocking event (always the actual event, explicit or inferred), to its
// property (a property instance or specification), and - except for restrict -
// to its pass action statement; assert and assume additionally carry an else
// (fail) statement. A cover reports whether it covers a sequence, every
// assertion reports whether its clock was inferred, and a restrict is not
// simulated and so has no pass/fail statement and generates no run-time
// information. These tests observe the production helpers in vpi.cpp and the
// VpiContext methods that apply those rules.

// Claim 1: the four directive kinds the diagram draws are concurrent
// assertions; the immediate kinds and sequence/property instances (the broader
// §37.49 class) and unrelated kinds are not.
TEST(ConcurrentAssertionModel, ConcurrentAssertionTypeCoversTheFourDirectives) {
  EXPECT_TRUE(VpiIsConcurrentAssertionType(vpiAssert));
  EXPECT_TRUE(VpiIsConcurrentAssertionType(vpiAssume));
  EXPECT_TRUE(VpiIsConcurrentAssertionType(vpiCover));
  EXPECT_TRUE(VpiIsConcurrentAssertionType(vpiRestrict));

  EXPECT_FALSE(VpiIsConcurrentAssertionType(vpiImmediateAssert));
  EXPECT_FALSE(VpiIsConcurrentAssertionType(vpiSequenceInst));
  EXPECT_FALSE(VpiIsConcurrentAssertionType(vpiPropertyInst));
  EXPECT_FALSE(VpiIsConcurrentAssertionType(vpiModule));
}

// Claim 8: vpiProperty reaches a property instance or a property specification;
// no other kind is a concurrent assertion's property.
TEST(ConcurrentAssertionModel, PropertyRelationTargetKinds) {
  EXPECT_TRUE(VpiIsConcurrentAssertionPropertyType(vpiPropertyInst));
  EXPECT_TRUE(VpiIsConcurrentAssertionPropertyType(vpiPropertySpec));

  EXPECT_FALSE(VpiIsConcurrentAssertionPropertyType(vpiSequenceInst));
  EXPECT_FALSE(VpiIsConcurrentAssertionPropertyType(vpiOperation));
}

// Claim 8: an assertion traverses through vpiProperty to its property
// instance/specification child, and reports none when no property is attached.
TEST(ConcurrentAssertionModel, AssertionReachesItsProperty) {
  VpiObject assertion;
  assertion.type = vpiAssert;
  VpiObject spec;
  spec.type = vpiPropertySpec;
  assertion.children = {&spec};
  EXPECT_EQ(VpiConcurrentAssertionProperty(&assertion), &spec);

  VpiObject with_inst;
  with_inst.type = vpiAssume;
  VpiObject inst;
  inst.type = vpiPropertyInst;
  with_inst.children = {&inst};
  EXPECT_EQ(VpiConcurrentAssertionProperty(&with_inst), &inst);

  VpiObject bare;
  bare.type = vpiCover;
  EXPECT_EQ(VpiConcurrentAssertionProperty(&bare), nullptr);
  EXPECT_EQ(VpiConcurrentAssertionProperty(nullptr), nullptr);
}

// Claim 2 + Detail 1: the same clocking event is reported whether it was
// written explicitly or inferred; the vpiIsClockInferred Boolean is what
// distinguishes the two, not the clocking-event traversal.
TEST(ConcurrentAssertionModel, ClockingEventIsTheActualEventForBothForms) {
  VpiContext ctx;

  VpiObject explicit_clk;
  explicit_clk.type = vpiAssert;
  VpiObject ev0;
  ev0.type = vpiEventControl;
  explicit_clk.children = {&ev0};
  EXPECT_EQ(VpiConcurrentAssertionClockingEvent(&explicit_clk), &ev0);
  EXPECT_EQ(ctx.Get(vpiIsClockInferred, &explicit_clk), 0);

  VpiObject inferred_clk;
  inferred_clk.type = vpiAssert;
  inferred_clk.clock_inferred = true;
  VpiObject ev1;
  ev1.type = vpiEventControl;
  inferred_clk.children = {&ev1};
  EXPECT_EQ(VpiConcurrentAssertionClockingEvent(&inferred_clk), &ev1);
  EXPECT_EQ(ctx.Get(vpiIsClockInferred, &inferred_clk), 1);
}

// Claim 2 edge: an assertion with no clocking event, and a null handle, report
// no clocking event.
TEST(ConcurrentAssertionModel, MissingClockingEventReportsNull) {
  VpiObject assertion;
  assertion.type = vpiAssume;
  EXPECT_EQ(VpiConcurrentAssertionClockingEvent(&assertion), nullptr);
  EXPECT_EQ(VpiConcurrentAssertionClockingEvent(nullptr), nullptr);
}

// Claim 4: a cover reports whether it covers a sequence through
// vpi_get(vpiIsCoverSequence).
TEST(ConcurrentAssertionModel, CoverReportsIsCoverSequence) {
  VpiContext ctx;
  VpiObject seq_cover;
  seq_cover.type = vpiCover;
  seq_cover.cover_sequence = true;
  EXPECT_EQ(ctx.Get(vpiIsCoverSequence, &seq_cover), 1);

  VpiObject prop_cover;
  prop_cover.type = vpiCover;
  EXPECT_EQ(ctx.Get(vpiIsCoverSequence, &prop_cover), 0);
}

// Claim 4 "false otherwise": vpiIsCoverSequence is meaningful only for a cover,
// so a concurrent assertion of a different kind (here an assert) reports 0 for
// the same property - the other input kind for the same query.
TEST(ConcurrentAssertionModel, NonCoverReportsIsCoverSequenceFalse) {
  VpiContext ctx;
  VpiObject assertion;
  assertion.type = vpiAssert;
  EXPECT_EQ(ctx.Get(vpiIsCoverSequence, &assertion), 0);

  VpiObject assume_obj;
  assume_obj.type = vpiAssume;
  EXPECT_EQ(ctx.Get(vpiIsCoverSequence, &assume_obj), 0);
}

// Claim 3 + Detail 2: assert, assume and cover carry a pass action statement; a
// restrict has none.
TEST(ConcurrentAssertionModel, PassStatementPresenceByKind) {
  EXPECT_TRUE(VpiConcurrentAssertionHasPassStmt(vpiAssert));
  EXPECT_TRUE(VpiConcurrentAssertionHasPassStmt(vpiAssume));
  EXPECT_TRUE(VpiConcurrentAssertionHasPassStmt(vpiCover));
  EXPECT_FALSE(VpiConcurrentAssertionHasPassStmt(vpiRestrict));
}

// Claim 5 + Detail 2: only assert and assume carry an else (fail) statement; a
// cover has no else statement and a restrict has no fail statement.
TEST(ConcurrentAssertionModel, ElseStatementPresenceByKind) {
  EXPECT_TRUE(VpiConcurrentAssertionHasElseStmt(vpiAssert));
  EXPECT_TRUE(VpiConcurrentAssertionHasElseStmt(vpiAssume));
  EXPECT_FALSE(VpiConcurrentAssertionHasElseStmt(vpiCover));
  EXPECT_FALSE(VpiConcurrentAssertionHasElseStmt(vpiRestrict));
}

// Claims 3 and 5: an assert traverses to its pass statement through vpiStmt and
// to its else statement through vpiElseStmt; each is null when absent.
TEST(ConcurrentAssertionModel, AssertReachesPassAndElseStatements) {
  VpiObject assertion;
  assertion.type = vpiAssert;
  VpiObject pass;
  pass.type = vpiStmt;
  VpiObject els;
  els.type = vpiElseStmt;
  assertion.children = {&pass, &els};

  EXPECT_EQ(VpiConcurrentAssertionStmt(&assertion), &pass);
  EXPECT_EQ(VpiConcurrentAssertionElseStmt(&assertion), &els);

  VpiObject pass_only;
  pass_only.type = vpiCover;
  VpiObject p2;
  p2.type = vpiStmt;
  pass_only.children = {&p2};
  EXPECT_EQ(VpiConcurrentAssertionStmt(&pass_only), &p2);
  EXPECT_EQ(VpiConcurrentAssertionElseStmt(&pass_only), nullptr);

  EXPECT_EQ(VpiConcurrentAssertionStmt(nullptr), nullptr);
  EXPECT_EQ(VpiConcurrentAssertionElseStmt(nullptr), nullptr);
}

// Detail 2: a restrict is not simulated and so generates no run-time
// information; the other concurrent assertion kinds are simulated.
TEST(ConcurrentAssertionModel, RestrictIsNotSimulated) {
  EXPECT_FALSE(VpiConcurrentAssertionIsSimulated(vpiRestrict));

  EXPECT_TRUE(VpiConcurrentAssertionIsSimulated(vpiAssert));
  EXPECT_TRUE(VpiConcurrentAssertionIsSimulated(vpiAssume));
  EXPECT_TRUE(VpiConcurrentAssertionIsSimulated(vpiCover));

  // A non-concurrent-assertion kind is not a simulated concurrent assertion.
  EXPECT_FALSE(VpiConcurrentAssertionIsSimulated(vpiModule));
}

// Claim 6: a concurrent assertion exposes its name and full name through
// vpi_get_str(vpiName/vpiFullName).
TEST(ConcurrentAssertionModel, AssertionReportsNameAndFullName) {
  VpiContext ctx;
  std::string name = "req_ack";
  VpiObject assertion;
  assertion.type = vpiAssert;
  assertion.name = name;
  assertion.full_name = "top.u_dut.req_ack";

  EXPECT_STREQ(ctx.GetStr(vpiName, &assertion), "req_ack");
  EXPECT_STREQ(ctx.GetStr(vpiFullName, &assertion), "top.u_dut.req_ack");
}

// Claim 8 edge: the property traversal matches by kind, so an assertion whose
// only child is an unrelated object reaches no property.
TEST(ConcurrentAssertionModel, PropertyTraversalSkipsNonPropertyChildren) {
  VpiObject assertion;
  assertion.type = vpiAssert;
  VpiObject net_child;
  net_child.type = vpiNet;
  assertion.children = {&net_child};
  EXPECT_EQ(VpiConcurrentAssertionProperty(&assertion), nullptr);
}

// Claim 2 edge: the clocking-event traversal matches the event-control child,
// so an assertion carrying only unrelated children reports no clocking event.
TEST(ConcurrentAssertionModel, ClockingEventTraversalSkipsNonEventChildren) {
  VpiObject assertion;
  assertion.type = vpiAssume;
  VpiObject prop_child;
  prop_child.type = vpiPropertySpec;
  assertion.children = {&prop_child};
  EXPECT_EQ(VpiConcurrentAssertionClockingEvent(&assertion), nullptr);
}

// Claims 3 and 5 edge: the pass- and else-statement traversals each match their
// own statement child, so an assertion with only unrelated children reaches
// neither a pass nor an else statement.
TEST(ConcurrentAssertionModel, StatementTraversalsSkipNonStatementChildren) {
  VpiObject assertion;
  assertion.type = vpiAssert;
  VpiObject net_child;
  net_child.type = vpiNet;
  assertion.children = {&net_child};
  EXPECT_EQ(VpiConcurrentAssertionStmt(&assertion), nullptr);
  EXPECT_EQ(VpiConcurrentAssertionElseStmt(&assertion), nullptr);
}

}  // namespace
}  // namespace delta
