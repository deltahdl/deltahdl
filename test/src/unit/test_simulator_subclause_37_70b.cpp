#include <gtest/gtest.h>

#include <cstddef>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

constexpr const char* kForms =
    "module top; bit a; int b;\n"
    "  initial forever #5 a = ~a;\n"
    "  always forever #5 b = 1;\n"
    "  initial forever begin : blk #5 b = 2; end\n"
    "  initial forever fork #5 b = 3; join\n"
    "  initial forever forever #5 b = 4;\n"
    "  initial forever if (a) #5 b = 5; else #5 b = 6;\n"
    "  initial forever case (a) 1: #5 b = 7; default: #5 b = 8; endcase\n"
    "  initial forever @(posedge a) b = 9;\n"
    "  initial begin b = 0; forever #5 b = 10; end\n"
    "  initial fork forever #5 b = 11; join_none\n"
    "  initial #100 $finish;\n"
    "endmodule\n";

class ForeverLoopsEverywhere : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    Run(kForms);
  }

  static vpiHandle ProcessBody(size_t n) {
    const std::vector<vpiHandle> kProcs = ObjectsOf(vpiProcess, By("top"));
    return n < kProcs.size() ? vpi_handle(vpiStmt, kProcs[n]) : nullptr;
  }

  static int BodyKindOf(vpiHandle loop) {
    if (loop == nullptr || vpi_get(vpiType, loop) != vpiForever) return 0;
    vpiHandle body = vpi_handle(vpiStmt, loop);
    return body == nullptr ? 0 : vpi_get(vpiType, body);
  }

  static vpiHandle LastInside(vpiHandle block) {
    if (block == nullptr) return nullptr;
    const std::vector<vpiHandle> kInner = ObjectsOf(vpiStmt, block);
    return kInner.empty() ? nullptr : kInner.back();
  }
};

TEST_F(ForeverLoopsEverywhere, ASingleStatementBodyIsReachedDirectly) {
  vpiHandle loop = ProcessBody(0);
  EXPECT_EQ(BodyKindOf(loop), vpiDelayControl);
  vpiHandle guarded = vpi_handle(vpiStmt, vpi_handle(vpiStmt, loop));
  ASSERT_NE(guarded, nullptr);
  EXPECT_EQ(vpi_get(vpiType, guarded), vpiAssignment);
}

TEST_F(ForeverLoopsEverywhere, AnAlwaysStatementCanBeAForever) {
  EXPECT_EQ(BodyKindOf(ProcessBody(1)), vpiDelayControl);
}

TEST_F(ForeverLoopsEverywhere, ANamedBlockBodyIsANamedBegin) {
  vpiHandle loop = ProcessBody(2);
  EXPECT_EQ(BodyKindOf(loop), vpiNamedBegin);
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiStmt, loop)), "blk");
}

TEST_F(ForeverLoopsEverywhere, AForkBodyIsAFork) {
  EXPECT_EQ(BodyKindOf(ProcessBody(3)), vpiFork);
}

TEST_F(ForeverLoopsEverywhere, ANestedForeverIsTheBodyOfTheOuterOne) {
  vpiHandle outer = ProcessBody(4);
  EXPECT_EQ(BodyKindOf(outer), vpiForever);
  EXPECT_EQ(BodyKindOf(vpi_handle(vpiStmt, outer)), vpiDelayControl);
}

TEST_F(ForeverLoopsEverywhere, AConditionalBodyIsAnIfElse) {
  EXPECT_EQ(BodyKindOf(ProcessBody(5)), vpiIfElse);
}

TEST_F(ForeverLoopsEverywhere, ACaseBodyIsACase) {
  EXPECT_EQ(BodyKindOf(ProcessBody(6)), vpiCase);
}

TEST_F(ForeverLoopsEverywhere, AnEventControlledBodyIsAnEventControl) {
  EXPECT_EQ(BodyKindOf(ProcessBody(7)), vpiEventControl);
}

TEST_F(ForeverLoopsEverywhere, AForeverAmongABlocksStatementsIsAForever) {
  vpiHandle block = ProcessBody(8);
  ASSERT_NE(block, nullptr);
  EXPECT_EQ(KindsOf(vpiStmt, block),
            (std::vector<int>{vpiAssignment, vpiForever}));
  EXPECT_EQ(BodyKindOf(LastInside(block)), vpiDelayControl);
}

TEST_F(ForeverLoopsEverywhere, AForeverInAForkIsAForever) {
  vpiHandle block = ProcessBody(9);
  ASSERT_NE(block, nullptr);
  EXPECT_EQ(vpi_get(vpiType, block), vpiFork);
  EXPECT_EQ(BodyKindOf(LastInside(block)), vpiDelayControl);
}

class ForeverLoopsInEachPlace : public VpiDesignRun {
 protected:
  static vpiHandle LoopOf(vpiHandle owner) {
    vpiHandle stmt = owner == nullptr ? nullptr : vpi_handle(vpiStmt, owner);
    if (stmt != nullptr && vpi_get(vpiType, stmt) == vpiBegin) {
      const std::vector<vpiHandle> kInner = ObjectsOf(vpiStmt, stmt);
      stmt = kInner.empty() ? nullptr : kInner[0];
    }
    return stmt;
  }

  static vpiHandle ProcessIn(const char* scope) {
    const std::vector<vpiHandle> kProcs = ObjectsOf(vpiProcess, By(scope));
    return kProcs.empty() ? nullptr : kProcs[0];
  }
};

TEST_F(ForeverLoopsInEachPlace, AForeverInEachPlaceReachesItsBody) {
  Run("package pk; int v; task pt; forever #5 v = 1; endtask endpackage\n"
      "interface ifc; int v; initial forever #5 v = 2; endinterface\n"
      "program prg; int v; initial forever #5 v = 3; endprogram\n"
      "module top; int v; ifc i0(); prg p0();\n"
      "  class C; int m; task ct; forever #5 m = 4; endtask endclass\n"
      "  task tk; forever #5 v = 5; endtask\n"
      "  function void fn; forever v = 6; endfunction\n"
      "  initial #100 $finish;\n"
      "endmodule\n");
  vpiHandle top = By("top");
  const struct {
    const char* where;
    vpiHandle loop;
    int body;
  } kPlaces[] = {
      {"pt", LoopOf(Named(vpiTask, By("pk"), "pt")), vpiDelayControl},
      {"i0", LoopOf(ProcessIn("top.i0")), vpiDelayControl},
      {"p0", LoopOf(ProcessIn("top.p0")), vpiDelayControl},
      {"ct", LoopOf(Named(vpiMethods, Named(vpiClassDefn, top, "C"), "ct")),
       vpiDelayControl},
      {"tk", LoopOf(Named(vpiTask, top, "tk")), vpiDelayControl},
      {"fn", LoopOf(Named(vpiFunction, top, "fn")), vpiAssignment},
  };
  for (const auto& place : kPlaces) {
    ASSERT_NE(place.loop, nullptr) << place.where;
    EXPECT_EQ(vpi_get(vpiType, place.loop), vpiForever) << place.where;
    vpiHandle body = vpi_handle(vpiStmt, place.loop);
    ASSERT_NE(body, nullptr) << place.where;
    EXPECT_EQ(vpi_get(vpiType, body), place.body) << place.where;
  }
}

}  // namespace
}  // namespace delta
