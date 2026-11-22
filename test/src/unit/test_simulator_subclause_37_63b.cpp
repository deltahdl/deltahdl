#include <gtest/gtest.h>

#include <cstddef>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class ProceduresEverywhere : public VpiDesignRun {
 protected:
  static void Walk(vpiHandle stmt, std::vector<vpiHandle>& out, int depth) {
    if (stmt == nullptr || depth > 8) return;
    out.push_back(stmt);
    Walk(vpi_handle(vpiStmt, stmt), out, depth + 1);
    Walk(vpi_handle(vpiElseStmt, stmt), out, depth + 1);
    for (vpiHandle inner : ObjectsOf(vpiStmt, stmt)) {
      Walk(inner, out, depth + 1);
    }
  }

  static std::vector<vpiHandle> StatementsOf(vpiHandle proc) {
    std::vector<vpiHandle> stmts;
    Walk(vpi_handle(vpiStmt, proc), stmts, 0);
    return stmts;
  }

  static void ExpectEachReaches(vpiHandle proc, size_t at_least) {
    ASSERT_NE(proc, nullptr);
    const std::vector<vpiHandle> kStmts = StatementsOf(proc);
    EXPECT_GE(kStmts.size(), at_least);
    for (vpiHandle stmt : kStmts) {
      EXPECT_EQ(VpiObjectOf(vpi_handle(vpiProcess, stmt)), VpiObjectOf(proc))
          << vpi_get(vpiType, stmt);
    }
  }

  static void ExpectBodyAndBack(vpiHandle proc, int body_type) {
    ASSERT_NE(proc, nullptr);
    vpiHandle body = vpi_handle(vpiStmt, proc);
    ASSERT_NE(body, nullptr) << vpi_get(vpiType, proc);
    EXPECT_EQ(vpi_get(vpiType, body), body_type);
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiProcess, body)), VpiObjectOf(proc));
  }
};

constexpr const char* kEveryKind =
    "module sub; logic a, b, c, d, e;\n"
    "  initial begin a = 0; end\n"
    "  final begin a = 1; end\n"
    "  always @(posedge c) begin a <= 1; end\n"
    "  always_comb begin b = c; end\n"
    "  always_ff @(posedge c) begin d <= c; end\n"
    "  always_latch begin if (c) e = c; end\n"
    "endmodule\n"
    "module top; logic a; initial a = 0; sub u(); endmodule\n";

TEST_F(ProceduresEverywhere, EveryProcedureKindIsItsOwnObject) {
  Run(kEveryKind);
  EXPECT_EQ(KindsOf(vpiProcess, By("top.u")),
            (std::vector<int>{vpiInitial, vpiFinal, vpiAlways, vpiAlways,
                              vpiAlways, vpiAlways}));
}

TEST_F(ProceduresEverywhere, AFinalReportsNoAlwaysType) {
  Run(kEveryKind);
  const std::vector<vpiHandle> kProcs = ObjectsOf(vpiProcess, By("top.u"));
  ASSERT_EQ(kProcs.size(), 6U);
  ASSERT_EQ(vpi_get(vpiType, kProcs[1]), vpiFinal);
  EXPECT_EQ(vpi_get(vpiAlwaysType, kProcs[1]), vpiUndefined);
}

TEST_F(ProceduresEverywhere, EveryProcedureKindReachesItsInstance) {
  Run(kEveryKind);
  vpiHandle sub = By("top.u");
  for (vpiHandle proc : ObjectsOf(vpiProcess, sub)) {
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiModule, proc)), VpiObjectOf(sub))
        << vpi_get(vpiType, proc);
  }
  for (vpiHandle proc : ObjectsOf(vpiProcess, By("top"))) {
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiModule, proc)), VpiObjectOf(By("top")));
  }
}

TEST_F(ProceduresEverywhere, EveryProcedureKindReachesItsBodyAndBack) {
  Run(kEveryKind);
  const std::vector<vpiHandle> kProcs = ObjectsOf(vpiProcess, By("top.u"));
  ASSERT_EQ(kProcs.size(), 6U);
  const std::vector<int> kBodies = {vpiBegin, vpiBegin,        vpiEventControl,
                                    vpiBegin, vpiEventControl, vpiBegin};
  for (size_t n = 0; n < kProcs.size(); ++n) {
    ExpectBodyAndBack(kProcs[n], kBodies[n]);
  }
}

TEST_F(ProceduresEverywhere, EachStatementOfEveryKindReachesItsProcedure) {
  Run(kEveryKind);
  const std::vector<vpiHandle> kProcs = ObjectsOf(vpiProcess, By("top.u"));
  ASSERT_EQ(kProcs.size(), 6U);
  for (vpiHandle proc : kProcs) ExpectEachReaches(proc, 2);
}

constexpr const char* kForks =
    "module top; logic a, b;\n"
    "  initial a = 0;\n"
    "  initial fork : f #1 a = 1; begin b = 1; end join\n"
    "  initial fork #2 b = 0; join\n"
    "endmodule\n";

TEST_F(ProceduresEverywhere, ANamedForkBodyReachesItsProcedureAndBack) {
  Run(kForks);
  const std::vector<vpiHandle> kProcs = ObjectsOf(vpiProcess, By("top"));
  ASSERT_EQ(kProcs.size(), 3U);
  ExpectBodyAndBack(kProcs[1], vpiNamedFork);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, kProcs[1])),
            VpiObjectOf(By("top.f")));
  ExpectBodyAndBack(kProcs[2], vpiFork);
}

TEST_F(ProceduresEverywhere, EachStatementOfAForkReachesItsProcedure) {
  Run(kForks);
  const std::vector<vpiHandle> kProcs = ObjectsOf(vpiProcess, By("top"));
  ASSERT_EQ(kProcs.size(), 3U);
  ExpectEachReaches(kProcs[1], 5);
  ExpectEachReaches(kProcs[2], 3);
}

constexpr const char* kPlaces =
    "interface ifc; logic y; initial begin y = 1; end endinterface\n"
    "program prg; logic y; initial begin y = 1; end final y = 0; endprogram\n"
    "module sub; logic y; if (1) begin : g initial begin y = 1; end end\n"
    "endmodule\n"
    "module top; ifc i0(); prg p0(); sub u(); endmodule\n";

TEST_F(ProceduresEverywhere, AProcedureInEachPlaceReachesItsBodyAndBack) {
  Run(kPlaces);
  for (const char* scope : {"top.i0", "top.p0", "top.u.g"}) {
    const std::vector<vpiHandle> kProcs = ObjectsOf(vpiProcess, By(scope));
    ASSERT_FALSE(kProcs.empty()) << scope;
    ExpectBodyAndBack(kProcs[0], vpiBegin);
    ExpectEachReaches(kProcs[0], 2);
  }
  const std::vector<vpiHandle> kProgram = ObjectsOf(vpiProcess, By("top.p0"));
  ASSERT_EQ(kProgram.size(), 2U);
  ExpectBodyAndBack(kProgram[1], vpiAssignment);
}

TEST_F(ProceduresEverywhere, AGeneratedProcedureReachesTheEnclosingModule) {
  Run(kPlaces);
  const std::vector<vpiHandle> kProcs = ObjectsOf(vpiProcess, By("top.u.g"));
  ASSERT_EQ(kProcs.size(), 1U);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiModule, kProcs[0])),
            VpiObjectOf(By("top.u")));
}

}  // namespace
}  // namespace delta
