#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "fixture_vpi_run.h"
#include "parser/ast_expr.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class ActiveTimeFormat : public ::testing::Test {
 protected:
  void SetUp() override {
    SetGlobalVpiContext(&ctx_);
    first_.kind = ExprKind::kSystemCall;
    first_.callee = "$timeformat";
    second_.kind = ExprKind::kSystemCall;
    second_.callee = "$timeformat";
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
  SimFixture f_;
  Expr first_;
  Expr second_;
};

TEST_F(ActiveTimeFormat, ReturnsNullWhenTimeformatNotCalled) {
  EXPECT_EQ(vpi_handle(vpiActiveTimeFormat, nullptr), nullptr);
}

TEST_F(ActiveTimeFormat, ReachesTheTimeformatCallThatSetTheFormat) {
  ctx_.NoteTimeFormatCall(&first_, f_.ctx);

  vpiHandle reached = vpi_handle(vpiActiveTimeFormat, nullptr);
  ASSERT_NE(reached, nullptr);
  EXPECT_EQ(vpi_get(vpiType, reached), vpiSysTaskCall);
  EXPECT_EQ(vpi_get_str(vpiName, reached), nullptr);
}

TEST_F(ActiveTimeFormat, ReachesTheLatestCallWhenTheTaskRunsAgain) {
  ctx_.NoteTimeFormatCall(&first_, f_.ctx);
  vpiHandle first = vpi_handle(vpiActiveTimeFormat, nullptr);
  ASSERT_NE(first, nullptr);

  ctx_.NoteTimeFormatCall(&second_, f_.ctx);
  vpiHandle second = vpi_handle(vpiActiveTimeFormat, nullptr);
  ASSERT_NE(second, nullptr);
  EXPECT_NE(second, first);
}

TEST_F(ActiveTimeFormat, DoesNotReachTheTimeformatCallFromANonNullReference) {
  ctx_.NoteTimeFormatCall(&first_, f_.ctx);
  vpiHandle recorded = vpi_handle(vpiActiveTimeFormat, nullptr);
  ASSERT_NE(recorded, nullptr);

  VpiObject some_object;
  some_object.type = vpiSysTaskCall;

  EXPECT_NE(vpi_handle(vpiActiveTimeFormat, VpiHandleOf(&some_object)),
            recorded);
}

TEST(ActiveTimeFormatSim, ADesignsTimeformatCallIsWhatTheEdgeReaches) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    $timeformat(-9, 2, \" ns\", 10);\n"
      "    $display(\"%t\", 5);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_EQ(out, "   5.00 ns\n");

  vpiHandle reached = vpi_handle(vpiActiveTimeFormat, nullptr);
  ASSERT_NE(reached, nullptr);
  EXPECT_EQ(vpi_get(vpiType, reached), vpiSysTaskCall);
  EXPECT_EQ(vpi_get_str(vpiName, reached), nullptr);
  EXPECT_STREQ(vpi_get_str(vpiDecompile, reached),
               "$timeformat(- 9, 2, \" ns\", 10)");

  SetGlobalVpiContext(nullptr);
}

TEST(ActiveTimeFormatSim, ADesignThatNeverCallsTheTaskReachesNothing) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $display(\"%t\", 3);\n"
      "endmodule\n",
      f);
  ASSERT_FALSE(out.empty());

  EXPECT_EQ(vpi_handle(vpiActiveTimeFormat, nullptr), nullptr);

  SetGlobalVpiContext(nullptr);
}

class ActiveTimeFormatOfAModel : public VpiDesignRun {
 protected:
  static std::vector<vpiHandle> BodiesOf(const std::string& scope) {
    std::vector<vpiHandle> bodies;
    for (vpiHandle process : ObjectsOf(vpiProcess, By(scope))) {
      bodies.push_back(vpi_handle(vpiStmt, process));
    }
    return bodies;
  }
};

TEST_F(ActiveTimeFormatOfAModel, TheEdgeReachesTheModelsCallStatement) {
  Run("module top;\n"
      "  initial $timeformat(-9, 2, \" ns\", 10);\n"
      "endmodule\n");
  const std::vector<vpiHandle> kBodies = BodiesOf("top");
  ASSERT_EQ(kBodies.size(), 1U);
  vpiHandle reached = vpi_handle(vpiActiveTimeFormat, nullptr);
  ASSERT_NE(reached, nullptr);
  EXPECT_EQ(vpi_compare_objects(reached, kBodies[0]), 1);
  EXPECT_EQ(vpi_get_str(vpiName, reached), nullptr);
  EXPECT_EQ(vpi_get(vpiLineNo, reached), 2);
}

TEST_F(ActiveTimeFormatOfAModel, TheEdgeReachesTheStatementOfTheLatestCall) {
  Run("module top;\n"
      "  initial $timeformat(-9, 2, \" ns\", 10);\n"
      "  initial #1 $timeformat(-6, 0, \" us\", 8);\n"
      "endmodule\n");
  vpiHandle reached = vpi_handle(vpiActiveTimeFormat, nullptr);
  ASSERT_NE(reached, nullptr);
  EXPECT_EQ(vpi_get(vpiLineNo, reached), 3);
  int matches = 0;
  for (vpiHandle body : BodiesOf("top")) {
    for (vpiHandle stmt : {body, vpi_handle(vpiStmt, body)}) {
      if (stmt != nullptr && vpi_compare_objects(reached, stmt) == 1) ++matches;
    }
  }
  EXPECT_EQ(matches, 1);
}

struct ReachedCall {
  int line;
  int type;
};

std::vector<ReachedCall> g_reached;

PLI_INT32 ProbeActiveTimeFormatCalltf(PLI_BYTE8*) {
  vpiHandle reached = vpi_handle(vpiActiveTimeFormat, nullptr);
  if (reached == nullptr) {
    g_reached.push_back({0, 0});
  } else {
    g_reached.push_back(
        {vpi_get(vpiLineNo, reached), vpi_get(vpiType, reached)});
  }
  return 0;
}

class ActiveTimeFormatInEachPlace : public ActiveTimeFormatOfAModel {
 protected:
  void SetUp() override {
    ActiveTimeFormatOfAModel::SetUp();
    g_reached.clear();
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText("$probe_format");
    data.calltf = &ProbeActiveTimeFormatCalltf;
    ASSERT_NE(vpi_register_systf(&data), nullptr);
  }
};

TEST_F(ActiveTimeFormatInEachPlace, EachPlacesCallIsReachedOnceItHasRun) {
  Run("package pk; task pt; $timeformat(-3, 0, \" ms\", 6); endtask\n"
      "endpackage\n"
      "interface ifc; initial #1 $timeformat(-6, 0, \" us\", 8);\n"
      "endinterface\n"
      "program pg; initial begin #3 $timeformat(-9, 0, \" ns\", 8); #9; end\n"
      "endprogram class C;\n"
      "  static function void cm; $timeformat(-12, 0, \" ps\", 8);\n"
      "  endfunction\n"
      "endclass\n"
      "module top;\n"
      "  ifc i0(); pg p0();\n"
      "  function void fv; $timeformat(-15, 0, \" fs\", 8); endfunction\n"
      "  initial begin\n"
      "    $probe_format; #2 $probe_format; #2 $probe_format;\n"
      "    pk::pt; $probe_format; C::cm(); $probe_format;\n"
      "    fv(); $probe_format;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_EQ(g_reached.size(), 6U);
  const std::vector<int> kLines = {0, 3, 5, 1, 7, 12};
  for (size_t i = 0; i < kLines.size(); ++i) {
    EXPECT_EQ(g_reached[i].line, kLines[i]) << "probe " << i;
    EXPECT_EQ(g_reached[i].type, kLines[i] == 0 ? 0 : vpiSysTaskCall)
        << "probe " << i;
  }
}

TEST_F(ActiveTimeFormatInEachPlace, DISABLED_ACallWithNoArgumentsIsReached) {
  Run("module top;\n"
      "  task tk; $timeformat; endtask\n"
      "  initial begin\n"
      "    $timeformat(-9, 2, \" ns\", 10); $probe_format;\n"
      "    tk; $probe_format;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_EQ(g_reached.size(), 2U);
  EXPECT_EQ(g_reached[0].line, 4);
  EXPECT_EQ(g_reached[1].line, 2);
  EXPECT_EQ(g_reached[1].type, vpiSysTaskCall);
  vpiHandle reached = vpi_handle(vpiActiveTimeFormat, nullptr);
  ASSERT_NE(reached, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiDecompile, reached), "$timeformat");
}

TEST_F(ActiveTimeFormatInEachPlace, ACallOnAPathThatNeverRunsIsNotReached) {
  Run("module top;\n"
      "  task never; $timeformat(-9, 2, \" ns\", 10); endtask\n"
      "  function void unused; $timeformat(-6, 0, \" us\", 8); endfunction\n"
      "  initial if (0) $timeformat(-3, 0, \" ms\", 6);\n"
      "  initial #1 $probe_format;\n"
      "endmodule\n");
  ASSERT_EQ(g_reached.size(), 1U);
  EXPECT_EQ(g_reached[0].line, 0);
  EXPECT_EQ(vpi_handle(vpiActiveTimeFormat, nullptr), nullptr);
}

TEST_F(ActiveTimeFormatInEachPlace, TheInstanceWhoseCallRanLastIsReached) {
  Run("module m #(parameter int D = 1);\n"
      "  initial #D $timeformat(-9, 2, \" ns\", 10);\n"
      "endmodule\n"
      "module top;\n"
      "  m #(2) a();\n"
      "  m #(1) b();\n"
      "endmodule\n");
  vpiHandle reached = vpi_handle(vpiActiveTimeFormat, nullptr);
  ASSERT_NE(reached, nullptr);
  const std::vector<vpiHandle> kInA = BodiesOf("top.a");
  const std::vector<vpiHandle> kInB = BodiesOf("top.b");
  ASSERT_EQ(kInA.size(), 1U);
  ASSERT_EQ(kInB.size(), 1U);
  vpiHandle call_in_a = vpi_handle(vpiStmt, kInA[0]);
  vpiHandle call_in_b = vpi_handle(vpiStmt, kInB[0]);
  ASSERT_NE(call_in_a, nullptr);
  ASSERT_NE(call_in_b, nullptr);
  EXPECT_EQ(vpi_compare_objects(reached, call_in_a), 1);
  EXPECT_EQ(vpi_compare_objects(reached, call_in_b), 0);
}

}  // namespace
}  // namespace delta
