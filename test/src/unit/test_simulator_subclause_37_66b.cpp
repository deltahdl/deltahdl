#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <utility>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class LoopsEverywhere : public VpiDesignRun {
 protected:
  static void Walk(vpiHandle stmt, std::vector<vpiHandle>& out, int depth) {
    if (stmt == nullptr || depth > 8) return;
    const int kType = vpi_get(vpiType, stmt);
    if (kType == vpiWhile || kType == vpiRepeat) out.push_back(stmt);
    Walk(vpi_handle(vpiStmt, stmt), out, depth + 1);
    for (vpiHandle inner : ObjectsOf(vpiStmt, stmt)) {
      Walk(inner, out, depth + 1);
    }
  }

  static std::vector<vpiHandle> LoopsUnder(vpiHandle owner) {
    std::vector<vpiHandle> out;
    if (owner != nullptr) Walk(vpi_handle(vpiStmt, owner), out, 0);
    return out;
  }

  static std::vector<vpiHandle> LoopBodies(int property) {
    std::vector<vpiHandle> out;
    for (vpiHandle proc : ObjectsOf(vpiProcess, By("top"))) {
      vpiHandle loop = vpi_handle(vpiStmt, proc);
      out.push_back(loop == nullptr ? nullptr : vpi_handle(property, loop));
    }
    return out;
  }

  static std::vector<int> TypesOf(const std::vector<vpiHandle>& objs) {
    std::vector<int> types;
    types.reserve(objs.size());
    for (vpiHandle obj : objs) {
      types.push_back(obj == nullptr ? 0 : vpi_get(vpiType, obj));
    }
    return types;
  }
};

constexpr const char* kWhileConditions =
    "module top; int i; parameter P = 0; logic [3:0] v; bit a, b, c = 1;\n"
    "  initial while (i) ;\n"
    "  initial while (P) ;\n"
    "  initial while (v[2]) ;\n"
    "  initial while (0) ;\n"
    "  initial while (a && b) ;\n"
    "  initial while (a || b) ;\n"
    "  initial while (!c) ;\n"
    "  initial while (i == 1) ;\n"
    "  initial while (i != 0) ;\n"
    "  initial while (|v) ;\n"
    "endmodule\n";

TEST_F(LoopsEverywhere, AWhileNamingAnObjectReachesIt) {
  Run(kWhileConditions);
  const std::vector<vpiHandle> kConditions = LoopBodies(vpiCondition);
  ASSERT_EQ(kConditions.size(), 10U);
  EXPECT_EQ(VpiObjectOf(kConditions[0]), VpiObjectOf(By("top.i")));
  EXPECT_EQ(VpiObjectOf(kConditions[1]), VpiObjectOf(By("top.P")));
  ASSERT_NE(kConditions[2], nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, kConditions[2])),
            VpiObjectOf(By("top.v")));
  EXPECT_EQ(IntegerOf(vpi_handle(vpiIndex, kConditions[2])), 2);
}

TEST_F(LoopsEverywhere, AWhileTestingAValueReachesIt) {
  Run(kWhileConditions);
  const std::vector<vpiHandle> kConditions = LoopBodies(vpiCondition);
  ASSERT_EQ(kConditions.size(), 10U);
  ASSERT_NE(kConditions[3], nullptr);
  EXPECT_EQ(vpi_get(vpiType, kConditions[3]), vpiConstant);
  EXPECT_EQ(IntegerOf(kConditions[3]), 0);
  std::vector<int> ops;
  for (size_t n = 4; n < kConditions.size(); ++n) {
    ops.push_back(kConditions[n] == nullptr ? 0 : OpOf(kConditions[n]));
  }
  EXPECT_EQ(ops, (std::vector<int>{vpiLogAndOp, vpiLogOrOp, vpiNotOp, vpiEqOp,
                                   vpiNeqOp, vpiUnaryOrOp}));
}

TEST_F(LoopsEverywhere, AWhileReachesTheBodyOfEachKind) {
  Run("module top; bit a, b; int x;\n"
      "  initial while (a) begin x = 1; end\n"
      "  initial while (a) begin : nb x = 2; end\n"
      "  initial while (a) fork x = 3; join\n"
      "  initial while (a) @(b) x = 4;\n"
      "  initial while (a) #1 x = 5;\n"
      "  initial while (a) ;\n"
      "endmodule\n");
  EXPECT_EQ(TypesOf(LoopBodies(vpiStmt)),
            (std::vector<int>{vpiBegin, vpiNamedBegin, vpiFork, vpiEventControl,
                              vpiDelayControl, vpiNullStmt}));
}

constexpr const char* kRepeats =
    "module top; parameter P = 2; int n = 1, x;\n"
    "  initial repeat (3) x = 1;\n"
    "  initial repeat (P) begin x = 2; end\n"
    "  initial repeat (n + 1) ;\n"
    "endmodule\n";

TEST_F(LoopsEverywhere, ARepeatReachesTheCountOfEachKind) {
  Run(kRepeats);
  const std::vector<vpiHandle> kCounts = LoopBodies(vpiCondition);
  ASSERT_EQ(kCounts.size(), 3U);
  ASSERT_NE(kCounts[0], nullptr);
  EXPECT_EQ(vpi_get(vpiType, kCounts[0]), vpiConstant);
  EXPECT_EQ(IntegerOf(kCounts[0]), 3);
  EXPECT_EQ(VpiObjectOf(kCounts[1]), VpiObjectOf(By("top.P")));
  ASSERT_NE(kCounts[2], nullptr);
  EXPECT_EQ(OpOf(kCounts[2]), vpiAddOp);
}

TEST_F(LoopsEverywhere, ARepeatReachesTheBodyOfEachKind) {
  Run(kRepeats);
  EXPECT_EQ(TypesOf(LoopBodies(vpiStmt)),
            (std::vector<int>{vpiAssignment, vpiBegin, vpiNullStmt}));
}

TEST_F(LoopsEverywhere, ALoopInEachPlaceReachesItsConditionAndBody) {
  Run("package pk; bit c; int v;\n"
      "  task pt; while (c) v = 1; repeat (2) v = 2; endtask\n"
      "  function void pf; while (c) v = 1; repeat (2) v = 2; endfunction\n"
      "endpackage\n"
      "interface ifc; bit c; int v;\n"
      "  initial begin while (c) v = 1; repeat (2) v = 2; end\n"
      "endinterface\n"
      "program prg; bit c; int v;\n"
      "  initial begin while (c) v = 1; repeat (2) v = 2; end\n"
      "endprogram\n"
      "module top; bit c; int v; ifc i0(); prg p0();\n"
      "  class C; bit c; int v;\n"
      "    task ct; while (c) v = 1; repeat (2) v = 2; endtask\n"
      "    function void cf; while (c) v = 1; repeat (2) v = 2; endfunction\n"
      "  endclass\n"
      "  task tk; while (c) v = 1; repeat (2) v = 2; endtask\n"
      "  function void fn; while (c) v = 1; repeat (2) v = 2; endfunction\n"
      "  always @(c) begin while (c) v = 1; repeat (2) v = 2; end\n"
      "  final begin while (c) v = 1; repeat (2) v = 2; end\n"
      "  initial if (c == 0) begin while (c) v = 1; repeat (2) v = 2; end\n"
      "  initial for (int k = 0; k < 1; k++) begin\n"
      "    while (c) v = 1; repeat (2) v = 2;\n"
      "  end\n"
      "endmodule\n");
  vpiHandle top = By("top");
  vpiHandle pk = By("pk");
  vpiHandle cls = Named(vpiClassDefn, top, "C");
  std::vector<std::pair<std::string, vpiHandle>> owners = {
      {"pt", Named(vpiTask, pk, "pt")},
      {"pf", Named(vpiFunction, pk, "pf")},
      {"ct", Named(vpiMethods, cls, "ct")},
      {"cf", Named(vpiMethods, cls, "cf")},
      {"tk", Named(vpiTask, top, "tk")},
      {"fn", Named(vpiFunction, top, "fn")},
  };
  for (const char* scope : {"top.i0", "top.p0", "top"}) {
    size_t n = 0;
    for (vpiHandle proc : ObjectsOf(vpiProcess, By(scope))) {
      owners.emplace_back(std::string(scope) + "#" + std::to_string(n++), proc);
    }
  }
  EXPECT_EQ(owners.size(), 12U);
  for (const auto& [where, owner] : owners) {
    const std::vector<vpiHandle> kLoops = LoopsUnder(owner);
    ASSERT_EQ(TypesOf(kLoops), (std::vector<int>{vpiWhile, vpiRepeat}))
        << where;
    vpiHandle tested = vpi_handle(vpiCondition, kLoops[0]);
    ASSERT_NE(tested, nullptr) << where;
    EXPECT_STREQ(vpi_get_str(vpiName, tested), "c") << where;
    EXPECT_EQ(IntegerOf(vpi_handle(vpiCondition, kLoops[1])), 2) << where;
    for (vpiHandle loop : kLoops) {
      vpiHandle body = vpi_handle(vpiStmt, loop);
      ASSERT_NE(body, nullptr) << where;
      EXPECT_EQ(vpi_get(vpiType, body), vpiAssignment) << where;
    }
  }
}

}  // namespace
}  // namespace delta
