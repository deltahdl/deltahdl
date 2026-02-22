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

struct SimCh511Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign *ElaborateSrc(const std::string &src, SimCh511Fixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

// §5.11 Array literals

// §5.11: Positional array literal — '{val, val, val} assigns each element.
TEST(SimCh511, ArrayLitPositional) {
  std::string src = "module m;\n"
                    "  logic [7:0] arr [0:2];\n"
                    "  initial begin\n"
                    "    arr = '{8'hAA, 8'hBB, 8'hCC};\n"
                    "  end\n"
                    "endmodule\n";
  SimCh511Fixture f;
  auto *design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0xAA);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0xBB);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0xCC);
}

// §5.11: Positional array literal in declaration initializer.
TEST(SimCh511, ArrayLitPositionalInit) {
  std::string src = "module m;\n"
                    "  logic [7:0] arr [0:2] = '{8'h11, 8'h22, 8'h33};\n"
                    "endmodule\n";
  SimCh511Fixture f;
  auto *design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0x11);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0x22);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0x33);
}

// §5.11: Replication in array literal — '{3{val}} fills all elements.
TEST(SimCh511, ArrayLitReplication) {
  std::string src = "module m;\n"
                    "  logic [7:0] arr [0:2];\n"
                    "  initial begin\n"
                    "    arr = '{3{8'hFF}};\n"
                    "  end\n"
                    "endmodule\n";
  SimCh511Fixture f;
  auto *design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0xFF);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0xFF);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0xFF);
}

// §5.11: Replication in declaration initializer.
TEST(SimCh511, ArrayLitReplicationInit) {
  std::string src = "module m;\n"
                    "  logic [7:0] arr [0:2] = '{3{8'hAA}};\n"
                    "endmodule\n";
  SimCh511Fixture f;
  auto *design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0xAA);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0xAA);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0xAA);
}

// §5.11: Default key — '{default:val} fills all array elements.
TEST(SimCh511, ArrayLitDefault) {
  std::string src = "module m;\n"
                    "  logic [7:0] arr [0:2];\n"
                    "  initial begin\n"
                    "    arr = '{default: 8'h42};\n"
                    "  end\n"
                    "endmodule\n";
  SimCh511Fixture f;
  auto *design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0x42);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0x42);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0x42);
}

// §5.11: Default key in declaration initializer.
TEST(SimCh511, ArrayLitDefaultInit) {
  std::string src = "module m;\n"
                    "  logic [7:0] arr [0:2] = '{default: 8'h99};\n"
                    "endmodule\n";
  SimCh511Fixture f;
  auto *design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0x99);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0x99);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0x99);
}

// §5.11: Index key with default — '{idx:val, default:val}.
TEST(SimCh511, ArrayLitIndexKeyDefault) {
  std::string src = "module m;\n"
                    "  logic [7:0] arr [0:2];\n"
                    "  initial begin\n"
                    "    arr = '{1: 8'hBB, default: 8'h00};\n"
                    "  end\n"
                    "endmodule\n";
  SimCh511Fixture f;
  auto *design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0x00);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0xBB);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0x00);
}

// §5.11: Index key in declaration initializer.
TEST(SimCh511, ArrayLitIndexKeyInit) {
  std::string src = "module m;\n"
                    "  logic [7:0] arr [0:2] = '{2: 8'hCC, default: 8'h11};\n"
                    "endmodule\n";
  SimCh511Fixture f;
  auto *design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0x11);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0x11);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0xCC);
}

// §5.11: Descending array range — '{val, val, val} maps left-to-right.
TEST(SimCh511, ArrayLitDescending) {
  std::string src = "module m;\n"
                    "  logic [7:0] arr [2:0] = '{8'hAA, 8'hBB, 8'hCC};\n"
                    "endmodule\n";
  SimCh511Fixture f;
  auto *design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  // Descending [2:0]: element 0 of pattern maps to index 2 (highest).
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0xAA);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0xBB);
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0xCC);
}

// §5.11: Type from assignment-like context (implicit from LHS).
TEST(SimCh511, ArrayLitTypeFromContext) {
  std::string src = "module m;\n"
                    "  logic [7:0] arr [0:1];\n"
                    "  initial begin\n"
                    "    arr = '{8'hDE, 8'hAD};\n"
                    "  end\n"
                    "endmodule\n";
  SimCh511Fixture f;
  auto *design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0xDE);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0xAD);
}
