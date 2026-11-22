#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class TriggersEverywhere : public VpiDesignRun {
 protected:
  static void Walk(vpiHandle stmt, std::vector<vpiHandle>& out, int depth) {
    if (stmt == nullptr || depth > 8) return;
    if (vpi_get(vpiType, stmt) == vpiEventStmt) out.push_back(stmt);
    Walk(vpi_handle(vpiStmt, stmt), out, depth + 1);
    for (vpiHandle inner : ObjectsOf(vpiStmt, stmt)) {
      Walk(inner, out, depth + 1);
    }
  }

  static std::vector<vpiHandle> TriggersUnder(vpiHandle routine) {
    std::vector<vpiHandle> stmts;
    if (routine != nullptr) Walk(vpi_handle(vpiStmt, routine), stmts, 0);
    return stmts;
  }

  static std::vector<vpiHandle> TriggersOfProcesses(vpiHandle scope) {
    std::vector<vpiHandle> stmts;
    if (scope == nullptr) return stmts;
    for (vpiHandle proc : ObjectsOf(vpiProcess, scope)) {
      Walk(vpi_handle(vpiStmt, proc), stmts, 0);
    }
    return stmts;
  }

  static std::vector<int> BlockingOf(const std::vector<vpiHandle>& stmts) {
    std::vector<int> blocking;
    blocking.reserve(stmts.size());
    for (vpiHandle stmt : stmts) blocking.push_back(vpi_get(vpiBlocking, stmt));
    return blocking;
  }

  static std::string EventNameOf(vpiHandle stmt) {
    vpiHandle event = vpi_handle(vpiNamedEvent, stmt);
    if (event == nullptr || vpi_get(vpiType, event) != vpiNamedEvent) {
      return "";
    }
    const char* full = vpi_get_str(vpiFullName, event);
    return full == nullptr ? "" : full;
  }

  static vpiHandle OnlyTrigger(vpiHandle scope) {
    const std::vector<vpiHandle> kStmts = TriggersOfProcesses(scope);
    EXPECT_EQ(kStmts.size(), 1U);
    return kStmts.empty() ? nullptr : kStmts[0];
  }
};

constexpr const char* kControlledTriggers =
    "module top; event e; logic clk;\n"
    "  initial begin ->> #1 e; ->> @(posedge clk) e; end\n"
    "endmodule\n";

TEST_F(TriggersEverywhere, AControlledNonblockingTriggerIsAnEventStatement) {
  Run(kControlledTriggers);
  EXPECT_EQ(TriggersOfProcesses(By("top")).size(), 2U);
}

TEST_F(TriggersEverywhere, AControlledNonblockingTriggerIsNotBlocking) {
  Run(kControlledTriggers);
  EXPECT_EQ(BlockingOf(TriggersOfProcesses(By("top"))),
            (std::vector<int>{0, 0}));
}

TEST_F(TriggersEverywhere, AControlledNonblockingTriggerReachesItsEvent) {
  Run(kControlledTriggers);
  const std::vector<vpiHandle> kStmts = TriggersOfProcesses(By("top"));
  ASSERT_EQ(kStmts.size(), 2U);
  for (vpiHandle stmt : kStmts) {
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiNamedEvent, stmt)),
              VpiObjectOf(By("top.e")));
  }
}

constexpr const char* kTriggersInEachPlace =
    "interface ifc; event e; initial begin -> e; ->> e; end endinterface\n"
    "program prg; event e; initial begin -> e; ->> e; end endprogram\n"
    "module top; event e; ifc i0(); prg p0();\n"
    "  class C; event ce; task ct; -> ce; ->> ce; endtask endclass\n"
    "  task tk; -> e; ->> e; endtask\n"
    "  function void fn; -> e; endfunction\n"
    "endmodule\n";

TEST_F(TriggersEverywhere, ATriggerInEachPlaceIsAnEventStatement) {
  Run(kTriggersInEachPlace);
  vpiHandle top = By("top");
  EXPECT_EQ(TriggersUnder(Named(vpiTask, top, "tk")).size(), 2U);
  EXPECT_EQ(TriggersUnder(Named(vpiFunction, top, "fn")).size(), 1U);
  EXPECT_EQ(
      TriggersUnder(Named(vpiMethods, Named(vpiClassDefn, top, "C"), "ct"))
          .size(),
      2U);
  EXPECT_EQ(TriggersOfProcesses(By("top.i0")).size(), 2U);
  EXPECT_EQ(TriggersOfProcesses(By("top.p0")).size(), 2U);
}

TEST_F(TriggersEverywhere, ATriggerInEachPlaceReportsItsBlocking) {
  Run(kTriggersInEachPlace);
  vpiHandle top = By("top");
  const std::vector<int> kBoth = {1, 0};
  EXPECT_EQ(BlockingOf(TriggersUnder(Named(vpiTask, top, "tk"))), kBoth);
  EXPECT_EQ(BlockingOf(TriggersUnder(Named(vpiFunction, top, "fn"))),
            (std::vector<int>{1}));
  EXPECT_EQ(BlockingOf(TriggersUnder(
                Named(vpiMethods, Named(vpiClassDefn, top, "C"), "ct"))),
            kBoth);
  EXPECT_EQ(BlockingOf(TriggersOfProcesses(By("top.i0"))), kBoth);
  EXPECT_EQ(BlockingOf(TriggersOfProcesses(By("top.p0"))), kBoth);
}

TEST_F(TriggersEverywhere, DISABLED_ATriggerInEachPlaceReachesItsEvent) {
  Run(kTriggersInEachPlace);
  vpiHandle top = By("top");
  const auto kExpectReaches = [](const std::vector<vpiHandle>& stmts,
                                 vpiHandle event, const char* where) {
    ASSERT_FALSE(stmts.empty()) << where;
    for (vpiHandle stmt : stmts) {
      EXPECT_EQ(VpiObjectOf(vpi_handle(vpiNamedEvent, stmt)),
                VpiObjectOf(event))
          << where;
    }
  };
  kExpectReaches(TriggersUnder(Named(vpiTask, top, "tk")), By("top.e"), "tk");
  kExpectReaches(TriggersUnder(Named(vpiFunction, top, "fn")), By("top.e"),
                 "fn");
  kExpectReaches(TriggersOfProcesses(By("top.i0")), By("top.i0.e"), "i0");
  kExpectReaches(TriggersOfProcesses(By("top.p0")), By("top.p0.e"), "p0");
  for (vpiHandle stmt :
       TriggersUnder(Named(vpiMethods, Named(vpiClassDefn, top, "C"), "ct"))) {
    vpiHandle event = vpi_handle(vpiNamedEvent, stmt);
    ASSERT_NE(event, nullptr);
    EXPECT_EQ(vpi_get(vpiType, event), vpiNamedEvent);
    EXPECT_STREQ(vpi_get_str(vpiName, event), "ce");
  }
}

TEST_F(TriggersEverywhere, ATriggerReachesTheDeclarationsOwnEvent) {
  Run("module top; event e; initial -> e; endmodule\n");
  vpiHandle declared = vpi_handle_by_name(VpiText("top.e"), nullptr);
  ASSERT_NE(declared, nullptr);
  vpiHandle stmt = OnlyTrigger(By("top"));
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiNamedEvent, stmt)),
            VpiObjectOf(declared));
}

TEST_F(TriggersEverywhere, DISABLED_ATriggerOfAnArrayElementReachesTheElement) {
  Run("module top; event evs [0:2]; initial -> evs[1]; endmodule\n");
  vpiHandle element = vpi_handle_by_index(By("top.evs"), 1);
  ASSERT_NE(element, nullptr);
  vpiHandle stmt = OnlyTrigger(By("top"));
  ASSERT_NE(stmt, nullptr);
  vpiHandle event = vpi_handle(vpiNamedEvent, stmt);
  ASSERT_NE(event, nullptr);
  EXPECT_EQ(vpi_get(vpiType, event), vpiNamedEvent);
  EXPECT_EQ(VpiObjectOf(event), VpiObjectOf(element));
}

TEST_F(TriggersEverywhere,
       DISABLED_ATriggerOfAClassPropertyReachesTheProperty) {
  Run("module top; class C; event ev; static event se; endclass\n"
      "  C h = new;\n"
      "  initial begin ->> h.ev; -> h.se; end\n"
      "endmodule\n");
  const std::vector<vpiHandle> kStmts = TriggersOfProcesses(By("top"));
  ASSERT_EQ(kStmts.size(), 2U);
  const char* names[] = {"ev", "se"};
  for (size_t n = 0; n < 2; ++n) {
    vpiHandle event = vpi_handle(vpiNamedEvent, kStmts[n]);
    ASSERT_NE(event, nullptr) << names[n];
    EXPECT_EQ(vpi_get(vpiType, event), vpiNamedEvent) << names[n];
    EXPECT_STREQ(vpi_get_str(vpiName, event), names[n]);
  }
}

TEST_F(TriggersEverywhere, DISABLED_ATriggerOfAnEventFormalReachesTheFormal) {
  Run("module top; event e;\n"
      "  task tk(event ev); -> ev; endtask\n"
      "  initial tk(e);\n"
      "endmodule\n");
  const std::vector<vpiHandle> kStmts =
      TriggersUnder(Named(vpiTask, By("top"), "tk"));
  ASSERT_EQ(kStmts.size(), 1U);
  EXPECT_EQ(EventNameOf(kStmts[0]), "top.tk.ev");
}

}  // namespace
}  // namespace delta
