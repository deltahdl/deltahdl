#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "fixture_vpi_run.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class EventStatement : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

TEST_F(EventStatement, EventStatementReportsBlockingFlagThroughVpiGet) {
  VpiObject blocking_trigger;
  blocking_trigger.type = vpiEventStmt;
  blocking_trigger.blocking = true;
  EXPECT_EQ(vpi_get(vpiBlocking, VpiHandleOf(&blocking_trigger)), 1);

  VpiObject nonblocking_trigger;
  nonblocking_trigger.type = vpiEventStmt;
  nonblocking_trigger.blocking = false;
  EXPECT_EQ(vpi_get(vpiBlocking, VpiHandleOf(&nonblocking_trigger)), 0);
}

TEST_F(EventStatement, BlockingIsUndefinedForNonEventStatement) {
  VpiObject not_an_event_stmt;
  not_an_event_stmt.type = vpiIf;
  not_an_event_stmt.blocking = true;
  EXPECT_EQ(vpi_get(vpiBlocking, VpiHandleOf(&not_an_event_stmt)),
            vpiUndefined);
}

std::vector<int> g_stmt_blocking;
std::vector<std::string> g_triggered_event_names;
std::vector<int> g_triggered_event_types;

void ReadEventStatements(vpiHandle stmt) {
  if (stmt == nullptr) return;
  const int kType = vpi_get(vpiType, stmt);
  if (kType == vpiEventStmt) {
    g_stmt_blocking.push_back(vpi_get(vpiBlocking, stmt));
    vpiHandle event = vpi_handle(vpiNamedEvent, stmt);
    g_triggered_event_types.push_back(event ? vpi_get(vpiType, event) : 0);
    const char* name = event ? vpi_get_str(vpiName, event) : nullptr;
    g_triggered_event_names.emplace_back(name ? name : "");
    return;
  }
  if (kType == vpiBegin || kType == vpiNamedBegin) {
    vpiHandle itr = vpi_iterate(vpiStmt, stmt);
    while (vpiHandle held = itr ? vpi_scan(itr) : nullptr) {
      ReadEventStatements(held);
    }
    return;
  }
  ReadEventStatements(vpi_handle(vpiStmt, stmt));
  ReadEventStatements(vpi_handle(vpiElseStmt, stmt));
}

PLI_INT32 ReadEventStatementsCalltf(PLI_BYTE8*) {
  vpiHandle mod = vpi_handle_by_name(VpiText("top"), nullptr);
  if (mod == nullptr) return 0;
  vpiHandle procs = vpi_iterate(vpiProcess, mod);
  if (procs == nullptr) return 0;
  ReadEventStatements(vpi_handle(vpiStmt, vpi_scan(procs)));
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

TEST_F(EventStatementOfADesign, BothTriggerFormsAreReadBackFromTheDesign) {
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$probe");
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
  EXPECT_EQ(g_stmt_blocking[0], 1);
  EXPECT_EQ(g_stmt_blocking[1], 0);

  ASSERT_EQ(g_triggered_event_types.size(), 2u);
  EXPECT_EQ(g_triggered_event_types[0], vpiNamedEvent);
  EXPECT_EQ(g_triggered_event_types[1], vpiNamedEvent);
  ASSERT_EQ(g_triggered_event_names.size(), 2u);
  EXPECT_EQ(g_triggered_event_names[0], "e");
  EXPECT_EQ(g_triggered_event_names[1], "e");
}

TEST_F(EventStatementOfADesign, ATriggerNestedInABlockIsFound) {
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$probe");
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

class EventStatementsOfARun : public VpiDesignRun {
 protected:
  static VpiObject* EventReachedFrom(vpiHandle scope) {
    vpiHandle it = vpi_iterate(vpiEventStmt, scope);
    vpiHandle stmt = it == nullptr ? nullptr : vpi_scan(it);
    return stmt == nullptr ? nullptr
                           : VpiObjectOf(vpi_handle(vpiNamedEvent, stmt));
  }
};

TEST_F(EventStatementsOfARun, AHierarchicalTriggerReachesItsEvent) {
  Run("module leaf; initial begin : b -> m.e; end endmodule\n"
      "module mid; event e; leaf s (); endmodule\n"
      "module top; mid m (); initial begin : b -> m.e; end endmodule\n");
  ASSERT_NE(By("top.m.e"), nullptr);
  EXPECT_EQ(EventReachedFrom(By("top.b")), VpiObjectOf(By("top.m.e")));
  EXPECT_EQ(EventReachedFrom(By("top.m.s.b")), VpiObjectOf(By("top.m.e")));
}

TEST_F(EventStatementsOfARun, ATriggerReachesTheEventItsBlockDeclares) {
  Run("module top; event e; initial begin : b event e; -> e; end endmodule\n");
  ASSERT_NE(By("top.b.e"), nullptr);
  EXPECT_EQ(EventReachedFrom(By("top.b")), VpiObjectOf(By("top.b.e")));
}

TEST_F(EventStatementsOfARun,
       ATriggerOfAnElementOrAPropertyIsAnEventStatement) {
  Run("module top; class H; event ev; endclass\n"
      "  event evs [2]; H h = new;\n"
      "  initial begin : b -> evs[0]; ->> h.ev; end\n"
      "endmodule\n");
  std::vector<int> blocking;
  vpiHandle it = vpi_iterate(vpiEventStmt, By("top.b"));
  ASSERT_NE(it, nullptr);
  while (vpiHandle stmt = vpi_scan(it)) {
    blocking.push_back(vpi_get(vpiBlocking, stmt));
  }
  EXPECT_EQ(blocking, (std::vector<int>{1, 0}));
}

}  // namespace
}  // namespace delta
