#include <gtest/gtest.h>

#include <cstring>
#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "simulation/lowerer.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"
#include "simulation/variable.h"

using namespace delta;

struct SimCh512Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign* ElaborateSrc(const std::string& src, SimCh512Fixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

// §5.12 Attributes

// §5.12: Attribute on variable declaration (LRM Example 5).
TEST(SimCh512, AttrOnVarDecl) {
  std::string src =
      "module m;\n"
      "  (* fsm_state *) logic [7:0] x = 8'hAB;\n"
      "endmodule\n";
  SimCh512Fixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("x")->value.ToUint64(), 0xAB);
}

// §5.12: Attribute with explicit value on declaration (LRM Example 5).
TEST(SimCh512, AttrWithValueOnDecl) {
  std::string src =
      "module m;\n"
      "  (* fsm_state = 1 *) logic [7:0] y = 8'hCD;\n"
      "endmodule\n";
  SimCh512Fixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("y")->value.ToUint64(), 0xCD);
}

// §5.12: Multiple attribute specs in one instance.
TEST(SimCh512, AttrMultipleSpecs) {
  std::string src =
      "module m;\n"
      "  (* full_case, parallel_case *) logic [7:0] z = 8'hEF;\n"
      "endmodule\n";
  SimCh512Fixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("z")->value.ToUint64(), 0xEF);
}

// §5.12: Multiple separate attribute instances (LRM Example 1 alt).
TEST(SimCh512, AttrMultipleInstances) {
  std::string src =
      "module m;\n"
      "  (* full_case = 1 *)\n"
      "  (* parallel_case = 1 *)\n"
      "  logic [7:0] w = 8'h77;\n"
      "endmodule\n";
  SimCh512Fixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("w")->value.ToUint64(), 0x77);
}

// §5.12: Attribute on initial block statement.
TEST(SimCh512, AttrOnInitialBlock) {
  std::string src =
      "module m;\n"
      "  logic [7:0] a;\n"
      "  (* synthesis_off *) initial begin\n"
      "    a = 8'h55;\n"
      "  end\n"
      "endmodule\n";
  SimCh512Fixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 0x55);
}

// §5.12: Attribute on assignment statement inside initial block.
TEST(SimCh512, AttrOnAssignStmt) {
  std::string src =
      "module m;\n"
      "  logic [7:0] b;\n"
      "  initial begin\n"
      "    (* mark *) b = 8'hDD;\n"
      "  end\n"
      "endmodule\n";
  SimCh512Fixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 0xDD);
}

// §5.12: Attribute on if statement.
TEST(SimCh512, AttrOnIfStmt) {
  std::string src =
      "module m;\n"
      "  logic [7:0] c;\n"
      "  initial begin\n"
      "    (* high_pri *) if (1) c = 8'hAA;\n"
      "    else c = 8'h00;\n"
      "  end\n"
      "endmodule\n";
  SimCh512Fixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 0xAA);
}

// §5.12: Attribute on case statement (LRM Example 1).
TEST(SimCh512, AttrOnCaseStmt) {
  std::string src =
      "module m;\n"
      "  logic [7:0] d;\n"
      "  initial begin\n"
      "    (* full_case, parallel_case *)\n"
      "    case (8'd2)\n"
      "      8'd1: d = 8'h11;\n"
      "      8'd2: d = 8'h22;\n"
      "      default: d = 8'h00;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n";
  SimCh512Fixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("d")->value.ToUint64(), 0x22);
}

// §5.12: Attribute on for loop statement.
TEST(SimCh512, AttrOnForLoop) {
  std::string src =
      "module m;\n"
      "  logic [7:0] e;\n"
      "  initial begin\n"
      "    e = 0;\n"
      "    (* unroll *) for (int i = 0; i < 3; i = i + 1)\n"
      "      e = e + 8'd1;\n"
      "  end\n"
      "endmodule\n";
  SimCh512Fixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("e")->value.ToUint64(), 3);
}

// §5.12: Attribute with string value (LRM Example 6).
TEST(SimCh512, AttrWithStringValue) {
  std::string src =
      "module m;\n"
      "  (* mode = \"fast\" *) logic [7:0] g = 8'h99;\n"
      "endmodule\n";
  SimCh512Fixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("g")->value.ToUint64(), 0x99);
}
