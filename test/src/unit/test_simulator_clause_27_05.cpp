// §27.5: Conditional generate constructs

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "simulation/lowerer.h"
#include "simulation/net.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"
#include "simulation/variable.h"

using namespace delta;

struct LowerFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign *ElaborateSrc(const std::string &src, LowerFixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

namespace {

TEST(Elaborator, GenerateIfTrueBranch) {
  LowerFixture f;
  auto *design = ElaborateSrc(
      "module t #(parameter N = 1) ();\n"
      "  logic [31:0] x;\n"
      "  generate\n"
      "    if (N > 0) begin\n"
      "      assign x = 42;\n"
      "    end else begin\n"
      "      assign x = 0;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(Elaborator, GenerateIfFalseBranch) {
  LowerFixture f;
  auto *design = ElaborateSrc(
      "module t #(parameter N = 0) ();\n"
      "  logic [31:0] x;\n"
      "  generate\n"
      "    if (N > 0) begin\n"
      "      assign x = 42;\n"
      "    end else begin\n"
      "      assign x = 99;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(Elaborator, GenerateCaseMatch) {
  LowerFixture f;
  auto *design = ElaborateSrc(
      "module t #(parameter MODE = 2) ();\n"
      "  logic [31:0] x;\n"
      "  generate\n"
      "    case (MODE)\n"
      "      1: begin assign x = 10; end\n"
      "      2: begin assign x = 20; end\n"
      "      3: begin assign x = 30; end\n"
      "    endcase\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(Elaborator, GenerateCaseDefault) {
  LowerFixture f;
  auto *design = ElaborateSrc(
      "module t #(parameter MODE = 99) ();\n"
      "  logic [31:0] x;\n"
      "  generate\n"
      "    case (MODE)\n"
      "      1: begin assign x = 10; end\n"
      "      2: begin assign x = 20; end\n"
      "      default: begin assign x = 77; end\n"
      "    endcase\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

}  // namespace
