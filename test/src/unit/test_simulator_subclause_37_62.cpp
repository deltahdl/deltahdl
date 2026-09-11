#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.62 Event statement: the object model diagram draws the event statement
// object traversing to the named event it triggers, and gives the event
// statement one property access edge - "-> blocking", bool: vpiBlocking. The
// event-stmt->named-event edge is the generic one-to-one traversal already
// provided by the data model (and the named event object is owned by §37.27);
// the clause's only owned content is the Boolean property. These tests observe
// the production code apply that property through the public
// vpi_get(vpiBlocking) dispatch path - both the value it reports for an event
// statement and the vpiUndefined it returns for an object kind the property is
// not drawn on.

// The fixture installs a context so the public vpi_get entry point runs its
// real dispatch over the test objects.
class EventStatement : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// Applied through the public dispatch: an event statement reports its blocking
// flag through vpi_get(vpiBlocking), as 1 for a blocking trigger (->) and 0 for
// a nonblocking trigger (->>). Driving both states exercises the production
// code reading the stored Boolean rather than a constant.
TEST_F(EventStatement, EventStatementReportsBlockingFlagThroughVpiGet) {
  VpiObject blocking_trigger;
  blocking_trigger.type = vpiEventStmt;
  blocking_trigger.blocking = true;
  EXPECT_EQ(vpi_get(vpiBlocking, &blocking_trigger), 1);

  VpiObject nonblocking_trigger;
  nonblocking_trigger.type = vpiEventStmt;
  nonblocking_trigger.blocking = false;
  EXPECT_EQ(vpi_get(vpiBlocking, &nonblocking_trigger), 0);
}

// Applied through the public dispatch: vpiBlocking is drawn only on the event
// statement object, so querying it on any other object kind is not a valid
// request and the production guard returns vpiUndefined rather than handing
// back a stored field. This distinguishes the clause's property edge, applied
// by the guard, from an unconditional field read.
TEST_F(EventStatement, BlockingIsUndefinedForNonEventStatement) {
  VpiObject not_an_event_stmt;
  not_an_event_stmt.type = vpiAssignment;
  EXPECT_EQ(vpi_get(vpiBlocking, &not_an_event_stmt), vpiUndefined);
}

// The clause against a described design. Everything above drives the property
// over objects a case built, and no pass under src/ ever built an event
// statement: vpi_get(vpiBlocking, stmt) reported vpiUndefined for every design
// there was, the figure's arrow to the named event reached nothing, and
// §38.36.1.3's cbStmt fan-out over a module's statements found none of the ones
// the source wrote. These cases read the clause back off a design.

// What the application found. A calltf is a plain C function with no return
// path to the case that provoked it.
std::vector<int> g_stmt_blocking;
std::vector<std::string> g_triggered_event_names;
std::vector<int> g_triggered_event_types;

int ReadEventStatementsCalltf(const char*) {
  vpiHandle mod = vpi_handle_by_name("top", nullptr);
  if (mod == nullptr) return 0;
  vpiHandle itr = vpi_iterate(vpiEventStmt, mod);
  if (itr == nullptr) return 0;
  while (vpiHandle stmt = vpi_scan(itr)) {
    // §37.62: the one property the figure draws on the event statement.
    g_stmt_blocking.push_back(vpi_get(vpiBlocking, stmt));
    // §37.4.3: the figure's untagged single arrow, walked with vpi_handle()
    // under the name of the enclosure it reaches.
    vpiHandle event = vpi_handle(vpiNamedEvent, stmt);
    g_triggered_event_types.push_back(event ? vpi_get(vpiType, event) : 0);
    const char* name = event ? vpi_get_str(vpiName, event) : nullptr;
    g_triggered_event_names.emplace_back(name ? name : "");
  }
  return 0;
}

class EventStatementOfADesign : public ::testing::Test {
 protected:
  void SetUp() override {
    SetGlobalVpiContext(&ctx_);
    g_stmt_blocking.clear();
    g_triggered_event_names.clear();
    g_triggered_event_types.clear();
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// The whole of §37.62 on a design that writes both trigger forms: each event
// statement the source wrote is an object of the figure's kind, the blocking
// property tells the two forms apart, and the arrow reaches the named event
// object the declaration itself stands as rather than a second object made for
// the trigger. The two forms trigger one event, so a traversal that reached
// some object of its own would be caught by the name as well as the kind.
TEST_F(EventStatementOfADesign, BothTriggerFormsAreReadBackFromTheDesign) {
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = "$probe";
  data.calltf = &ReadEventStatementsCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);

  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  event e;\n"
      "  initial begin\n"
      "    $probe;\n"
      "    -> e;\n"
      "    ->> e;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  ASSERT_EQ(g_stmt_blocking.size(), 2u);
  // §9.7.2: "->" is the blocking trigger, "->>" the nonblocking one.
  EXPECT_EQ(g_stmt_blocking[0], 1);
  EXPECT_EQ(g_stmt_blocking[1], 0);

  ASSERT_EQ(g_triggered_event_types.size(), 2u);
  EXPECT_EQ(g_triggered_event_types[0], vpiNamedEvent);
  EXPECT_EQ(g_triggered_event_types[1], vpiNamedEvent);
  ASSERT_EQ(g_triggered_event_names.size(), 2u);
  EXPECT_EQ(g_triggered_event_names[0], "e");
  EXPECT_EQ(g_triggered_event_names[1], "e");
}

// A trigger nested inside a block within the procedure is an event statement of
// the design as much as one written at the top of it, so the walk descends
// rather than reading the body's first level.
TEST_F(EventStatementOfADesign, ATriggerNestedInABlockIsFound) {
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = "$probe";
  data.calltf = &ReadEventStatementsCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);

  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  event e;\n"
      "  bit c;\n"
      "  initial begin\n"
      "    $probe;\n"
      "    if (c) -> e;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  ASSERT_EQ(g_stmt_blocking.size(), 1u);
  EXPECT_EQ(g_stmt_blocking[0], 1);
  ASSERT_EQ(g_triggered_event_names.size(), 1u);
  EXPECT_EQ(g_triggered_event_names[0], "e");
}

}  // namespace
}  // namespace delta
