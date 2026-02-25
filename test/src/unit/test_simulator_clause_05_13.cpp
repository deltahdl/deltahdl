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

struct SimCh513Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign* ElaborateSrc(const std::string& src, SimCh513Fixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

// §5.13 Built-in methods

// §5.13: Built-in method call with dot notation and parentheses — arr.size().
TEST(SimCh513, BuiltinMethodCallWithParens) {
  std::string src =
      "module m;\n"
      "  logic [7:0] arr [0:3];\n"
      "  logic [31:0] s;\n"
      "  initial begin\n"
      "    s = arr.size();\n"
      "  end\n"
      "endmodule\n";
  SimCh513Fixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("s")->value.ToUint64(), 4u);
}

// §5.13: Optional empty parentheses — arr.size (property syntax, no parens).
TEST(SimCh513, BuiltinMethodNoParens) {
  std::string src =
      "module m;\n"
      "  logic [7:0] arr [0:2];\n"
      "  logic [31:0] s;\n"
      "  initial begin\n"
      "    s = arr.size;\n"
      "  end\n"
      "endmodule\n";
  SimCh513Fixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("s")->value.ToUint64(), 3u);
}

// §5.13: Method result used in an expression — arr.size() + 1.
TEST(SimCh513, BuiltinMethodInExpr) {
  std::string src =
      "module m;\n"
      "  logic [7:0] arr [0:4];\n"
      "  logic [31:0] r;\n"
      "  initial begin\n"
      "    r = arr.size() + 32'd1;\n"
      "  end\n"
      "endmodule\n";
  SimCh513Fixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("r")->value.ToUint64(), 6u);
}

// §5.13: Built-in method on queue — q.size() returns element count.
TEST(SimCh513, BuiltinMethodOnQueue) {
  std::string src =
      "module m;\n"
      "  logic [7:0] q [$];\n"
      "  logic [31:0] s;\n"
      "  initial begin\n"
      "    q.push_back(8'hAA);\n"
      "    q.push_back(8'hBB);\n"
      "    s = q.size();\n"
      "  end\n"
      "endmodule\n";
  SimCh513Fixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("s")->value.ToUint64(), 2u);
}

// §5.13: Built-in method with argument — q.push_back(val) modifies queue.
TEST(SimCh513, BuiltinMethodWithArg) {
  std::string src =
      "module m;\n"
      "  logic [7:0] q [$];\n"
      "  initial begin\n"
      "    q.push_back(8'h42);\n"
      "    q.push_back(8'h43);\n"
      "    q.push_back(8'h44);\n"
      "  end\n"
      "endmodule\n";
  SimCh513Fixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 0x42u);
  EXPECT_EQ(q->elements[1].ToUint64(), 0x43u);
  EXPECT_EQ(q->elements[2].ToUint64(), 0x44u);
}

// §5.13: Reduction built-in method — arr.sum() on fixed array.
TEST(SimCh513, BuiltinMethodReduction) {
  std::string src =
      "module m;\n"
      "  logic [7:0] arr [0:2] = '{8'd10, 8'd20, 8'd30};\n"
      "  logic [31:0] total;\n"
      "  initial begin\n"
      "    total = arr.sum();\n"
      "  end\n"
      "endmodule\n";
  SimCh513Fixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("total")->value.ToUint64(), 60u);
}

// §5.13: Mutating built-in method — arr.reverse() reorders elements.
TEST(SimCh513, BuiltinMethodMutating) {
  std::string src =
      "module m;\n"
      "  logic [7:0] arr [0:2] = '{8'hAA, 8'hBB, 8'hCC};\n"
      "  initial begin\n"
      "    arr.reverse();\n"
      "  end\n"
      "endmodule\n";
  SimCh513Fixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0xCC);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0xBB);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0xAA);
}

// §5.13: Mutating method without parens — arr.reverse (property syntax).
TEST(SimCh513, BuiltinMethodMutatingNoParens) {
  std::string src =
      "module m;\n"
      "  logic [7:0] arr [0:2] = '{8'h11, 8'h22, 8'h33};\n"
      "  initial begin\n"
      "    arr.reverse;\n"
      "  end\n"
      "endmodule\n";
  SimCh513Fixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0x33);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0x22);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0x11);
}

// §5.13: Dynamic array method — dyn.size() returns dynamic array length.
TEST(SimCh513, BuiltinMethodDynArray) {
  std::string src =
      "module m;\n"
      "  logic [7:0] dyn [] = '{8'hDE, 8'hAD};\n"
      "  logic [31:0] s;\n"
      "  initial begin\n"
      "    s = dyn.size();\n"
      "  end\n"
      "endmodule\n";
  SimCh513Fixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("s")->value.ToUint64(), 2u);
}

// §5.13: Queue pop_front — void mutating method with implicit return.
TEST(SimCh513, BuiltinMethodQueuePopFront) {
  std::string src =
      "module m;\n"
      "  logic [7:0] q [$];\n"
      "  logic [31:0] s;\n"
      "  initial begin\n"
      "    q.push_back(8'h10);\n"
      "    q.push_back(8'h20);\n"
      "    q.push_back(8'h30);\n"
      "    q.pop_front();\n"
      "    s = q.size();\n"
      "  end\n"
      "endmodule\n";
  SimCh513Fixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("s")->value.ToUint64(), 2u);
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->elements[0].ToUint64(), 0x20u);
  EXPECT_EQ(q->elements[1].ToUint64(), 0x30u);
}
