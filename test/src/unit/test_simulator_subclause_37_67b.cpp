#include <gtest/gtest.h>

#include <cstddef>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

constexpr const char* kForms =
    "module sub; event a, b; endmodule\n"
    "module top; event a, b; bit c; int x, y, r; sub u();\n"
    "  initial begin wait_order (a, b) r = 1; x = 9; end\n"
    "  initial begin wait (c == 1) x = 1; y = 9; end\n"
    "  initial begin fork #1; join_none wait fork; y = 9; end\n"
    "  initial begin wait (c); y = 9; end\n"
    "  initial begin wait_order (a, b); y = 9; end\n"
    "  initial begin wait (x == y) r = 2; end\n"
    "  initial begin wait_order (u.a, u.b) r = 3; end\n"
    "endmodule\n";

class WaitsEverywhere : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    Run(kForms);
  }

  static vpiHandle FirstOfBlock(size_t n) {
    const std::vector<vpiHandle> kProcs = ObjectsOf(vpiProcess, By("top"));
    if (n >= kProcs.size()) return nullptr;
    const std::vector<vpiHandle> kStmts =
        ObjectsOf(vpiStmt, vpi_handle(vpiStmt, kProcs[n]));
    for (vpiHandle stmt : kStmts) {
      const int kType = vpi_get(vpiType, stmt);
      if (kType == vpiWait || kType == vpiWaitFork || kType == vpiOrderedWait) {
        return stmt;
      }
    }
    return nullptr;
  }

  static vpiHandle EventOf(vpiHandle obj) {
    if (obj != nullptr && vpi_get(vpiType, obj) == vpiRefObj) {
      return vpi_handle(vpiActual, obj);
    }
    return obj;
  }
};

TEST_F(WaitsEverywhere, AnOrderedWaitWithoutAnElseHasNoElseStmt) {
  vpiHandle wait = FirstOfBlock(0);
  ASSERT_NE(wait, nullptr);
  EXPECT_EQ(vpi_get(vpiType, wait), vpiOrderedWait);
  vpiHandle action = vpi_handle(vpiStmt, wait);
  ASSERT_NE(action, nullptr);
  EXPECT_EQ(vpi_get(vpiType, action), vpiAssignment);
  EXPECT_EQ(vpi_handle(vpiElseStmt, wait), nullptr);
}

TEST_F(WaitsEverywhere, AWaitAndAWaitForkHaveNoElseStmt) {
  vpiHandle wait = FirstOfBlock(1);
  vpiHandle wait_fork = FirstOfBlock(2);
  ASSERT_NE(wait, nullptr);
  ASSERT_NE(wait_fork, nullptr);
  EXPECT_EQ(vpi_get(vpiType, wait), vpiWait);
  EXPECT_EQ(vpi_get(vpiType, wait_fork), vpiWaitFork);
  EXPECT_EQ(vpi_handle(vpiElseStmt, wait), nullptr);
  EXPECT_EQ(vpi_handle(vpiElseStmt, wait_fork), nullptr);
}

TEST_F(WaitsEverywhere, AWaitOnANullStatementGuardsNoOtherStatement) {
  vpiHandle wait = FirstOfBlock(3);
  ASSERT_NE(wait, nullptr);
  EXPECT_EQ(vpi_get(vpiType, wait), vpiWait);
  vpiHandle guarded = vpi_handle(vpiStmt, wait);
  if (guarded != nullptr) EXPECT_EQ(vpi_get(vpiType, guarded), vpiNullStmt);
}

TEST_F(WaitsEverywhere, AnOrderedWaitWithNoActionGuardsNothing) {
  vpiHandle wait = FirstOfBlock(4);
  ASSERT_NE(wait, nullptr);
  EXPECT_EQ(vpi_get(vpiType, wait), vpiOrderedWait);
  EXPECT_EQ(vpi_handle(vpiStmt, wait), nullptr);
  EXPECT_EQ(vpi_handle(vpiElseStmt, wait), nullptr);
}

TEST_F(WaitsEverywhere, AWaitForkGuardsNothing) {
  vpiHandle wait_fork = FirstOfBlock(2);
  ASSERT_NE(wait_fork, nullptr);
  EXPECT_EQ(vpi_handle(vpiStmt, wait_fork), nullptr);
}

TEST_F(WaitsEverywhere, AWaitOnAnEqualityReachesTheOperation) {
  vpiHandle wait = FirstOfBlock(5);
  ASSERT_NE(wait, nullptr);
  vpiHandle condition = vpi_handle(vpiCondition, wait);
  ASSERT_NE(condition, nullptr);
  EXPECT_EQ(vpi_get(vpiType, condition), vpiOperation);
  EXPECT_EQ(OpOf(condition), vpiEqOp);
  const std::vector<vpiHandle> kOperands = OperandsOf(condition);
  ASSERT_EQ(kOperands.size(), 2U);
  EXPECT_EQ(VpiObjectOf(kOperands[0]), VpiObjectOf(By("top.x")));
  EXPECT_EQ(VpiObjectOf(kOperands[1]), VpiObjectOf(By("top.y")));
}

TEST_F(WaitsEverywhere, AnOrderedWaitIteratesHierarchicalEventsInOrder) {
  vpiHandle wait = FirstOfBlock(6);
  ASSERT_NE(wait, nullptr);
  vpiHandle it = vpi_iterate(vpiCondition, wait);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(VpiObjectOf(EventOf(vpi_scan(it))), VpiObjectOf(By("top.u.a")));
  EXPECT_EQ(VpiObjectOf(EventOf(vpi_scan(it))), VpiObjectOf(By("top.u.b")));
  EXPECT_EQ(vpi_scan(it), nullptr);
}

class WaitsOnASequence : public VpiDesignRun {};

TEST_F(WaitsOnASequence,
       DISABLED_AWaitOnATriggeredSequenceReachesItsCondition) {
  Run("module top; bit clk, c; int x;\n"
      "  sequence s; @(posedge clk) c; endsequence\n"
      "  initial wait (s.triggered) x = 1;\n"
      "endmodule\n");
  const std::vector<vpiHandle> kProcs = ObjectsOf(vpiProcess, By("top"));
  ASSERT_EQ(kProcs.size(), 1U);
  vpiHandle wait = vpi_handle(vpiStmt, kProcs[0]);
  ASSERT_NE(wait, nullptr);
  EXPECT_EQ(vpi_get(vpiType, wait), vpiWait);
  EXPECT_NE(vpi_handle(vpiCondition, wait), nullptr);
}

class WaitsInEachPlace : public VpiDesignRun {
 protected:
  static std::vector<int> WaitKindsUnder(vpiHandle owner) {
    std::vector<int> kinds;
    vpiHandle body = owner == nullptr ? nullptr : vpi_handle(vpiStmt, owner);
    if (body == nullptr) return kinds;
    for (vpiHandle stmt : ObjectsOf(vpiStmt, body)) {
      const int kType = vpi_get(vpiType, stmt);
      if (kType == vpiWait || kType == vpiWaitFork || kType == vpiOrderedWait) {
        kinds.push_back(kType);
      }
    }
    return kinds;
  }

  static vpiHandle OnlyProcess(const char* scope) {
    const std::vector<vpiHandle> kProcs = ObjectsOf(vpiProcess, By(scope));
    return kProcs.size() == 1 ? kProcs[0] : nullptr;
  }
};

TEST_F(WaitsInEachPlace, EachWaitKindIsItsOwnObjectInEachPlace) {
  Run("package pk; bit c; event a, b;\n"
      "  task pt; wait (c); wait fork; wait_order (a, b); endtask\n"
      "endpackage\n"
      "interface ifc; bit c; event a, b;\n"
      "  initial begin wait (c); wait fork; wait_order (a, b); end\n"
      "endinterface\n"
      "program prg; bit c; event a, b;\n"
      "  initial begin wait (c); wait fork; wait_order (a, b); end\n"
      "endprogram\n"
      "module top; bit c; event a, b; ifc i0(); prg p0();\n"
      "  class C; bit c; event a, b;\n"
      "    task ct; wait (c); wait fork; wait_order (a, b); endtask\n"
      "  endclass\n"
      "  task tk; wait (c); wait fork; wait_order (a, b); endtask\n"
      "endmodule\n");
  vpiHandle top = By("top");
  const struct {
    const char* where;
    vpiHandle owner;
  } kPlaces[] = {
      {"pt", Named(vpiTask, By("pk"), "pt")},
      {"i0", OnlyProcess("top.i0")},
      {"p0", OnlyProcess("top.p0")},
      {"ct", Named(vpiMethods, Named(vpiClassDefn, top, "C"), "ct")},
      {"tk", Named(vpiTask, top, "tk")},
  };
  for (const auto& place : kPlaces) {
    EXPECT_EQ(WaitKindsUnder(place.owner),
              (std::vector<int>{vpiWait, vpiWaitFork, vpiOrderedWait}))
        << place.where;
  }
}

}  // namespace
}  // namespace delta
