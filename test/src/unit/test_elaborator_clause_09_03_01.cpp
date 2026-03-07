#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §9.3.1: Sequential block elaborates within an initial process.
TEST(ElabClause09_03_01, SeqBlockInInitialElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int a;\n"
      "  initial begin\n"
      "    a = 10;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  bool found = false;
  for (auto& p : design->top_modules[0]->processes) {
    if (p.kind == RtlirProcessKind::kInitial) found = true;
  }
  EXPECT_TRUE(found);
}

// §9.3.1: Nested sequential blocks elaborate without errors.
TEST(ElabClause09_03_01, NestedSeqBlocksElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int a, b, c;\n"
      "  initial begin\n"
      "    begin\n"
      "      a = 10;\n"
      "      b = 20;\n"
      "    end\n"
      "    c = a + b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §9.3.1: Sequential block with variable declarations elaborates.
TEST(ElabClause09_03_01, SeqBlockWithVarDeclElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int x;\n"
      "  initial begin\n"
      "    int local_var;\n"
      "    local_var = 42;\n"
      "    x = local_var;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §9.3.1: Sequential block in always_comb elaborates correctly.
TEST(ElabClause09_03_01, SeqBlockInAlwaysComb) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b, c;\n"
      "  always_comb begin\n"
      "    a = b;\n"
      "    c = a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §9.3.1: Simulator verifies sequential execution order.
TEST(SimCh10, BlockingAssignBeginEnd) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a, b, c;\n"
      "  initial begin\n"
      "    begin\n"
      "      a = 10;\n"
      "      b = 20;\n"
      "      c = a + b;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* c = f.ctx.FindVariable("c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(c->value.ToUint64(), 30u);
}

}  // namespace
