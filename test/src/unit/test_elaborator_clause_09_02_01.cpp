#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(InitialProcedureElaboration, InitialElaboratesToCorrectKind) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  initial a = 0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto& procs = design->top_modules[0]->processes;
  ASSERT_EQ(procs.size(), 1u);
  EXPECT_EQ(procs[0].kind, RtlirProcessKind::kInitial);
  EXPECT_NE(procs[0].body, nullptr);
}

TEST(InitialProcedureElaboration, InitialHasNoSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  initial begin\n"
      "    a = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  auto& procs = design->top_modules[0]->processes;
  ASSERT_EQ(procs.size(), 1u);
  EXPECT_TRUE(procs[0].sensitivity.empty());
}

TEST(InitialProcedureElaboration, MultipleInitialsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial a = 0;\n"
      "  initial b = 1;\n"
      "  initial c = 2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  int count = 0;
  for (auto& p : design->top_modules[0]->processes) {
    if (p.kind == RtlirProcessKind::kInitial) ++count;
  }
  EXPECT_EQ(count, 3);
}

TEST(InitialProcedureElaboration, NullStatementInitialElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial ;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto& procs = design->top_modules[0]->processes;
  ASSERT_EQ(procs.size(), 1u);
  EXPECT_EQ(procs[0].kind, RtlirProcessKind::kInitial);
  EXPECT_NE(procs[0].body, nullptr);
}

TEST(InitialProcedureElaboration, BeginEndBodyPreserved) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    a = 0;\n"
      "    b = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto& procs = design->top_modules[0]->processes;
  ASSERT_EQ(procs.size(), 1u);
  EXPECT_EQ(procs[0].body->kind, StmtKind::kBlock);
}

}  // namespace
