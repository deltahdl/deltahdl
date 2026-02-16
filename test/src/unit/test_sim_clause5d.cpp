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

struct SimCh5dFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign* ElaborateSrc(const std::string& src, SimCh5dFixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

// ===== §5.11 Array literals =====

// §5.11: Positional array literal — '{val, val, val} assigns each element.
TEST(SimCh5d, ArrayLitPositional) {
  std::string src =
      "module m;\n"
      "  logic [7:0] arr [0:2];\n"
      "  initial begin\n"
      "    arr = '{8'hAA, 8'hBB, 8'hCC};\n"
      "  end\n"
      "endmodule\n";
  SimCh5dFixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0xAA);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0xBB);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0xCC);
}

// §5.11: Positional array literal in declaration initializer.
TEST(SimCh5d, ArrayLitPositionalInit) {
  std::string src =
      "module m;\n"
      "  logic [7:0] arr [0:2] = '{8'h11, 8'h22, 8'h33};\n"
      "endmodule\n";
  SimCh5dFixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0x11);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0x22);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0x33);
}

// §5.11: Replication in array literal — '{3{val}} fills all elements.
TEST(SimCh5d, ArrayLitReplication) {
  std::string src =
      "module m;\n"
      "  logic [7:0] arr [0:2];\n"
      "  initial begin\n"
      "    arr = '{3{8'hFF}};\n"
      "  end\n"
      "endmodule\n";
  SimCh5dFixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0xFF);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0xFF);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0xFF);
}

// §5.11: Replication in declaration initializer.
TEST(SimCh5d, ArrayLitReplicationInit) {
  std::string src =
      "module m;\n"
      "  logic [7:0] arr [0:2] = '{3{8'hAA}};\n"
      "endmodule\n";
  SimCh5dFixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0xAA);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0xAA);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0xAA);
}

// §5.11: Default key — '{default:val} fills all array elements.
TEST(SimCh5d, ArrayLitDefault) {
  std::string src =
      "module m;\n"
      "  logic [7:0] arr [0:2];\n"
      "  initial begin\n"
      "    arr = '{default: 8'h42};\n"
      "  end\n"
      "endmodule\n";
  SimCh5dFixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0x42);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0x42);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0x42);
}

// §5.11: Default key in declaration initializer.
TEST(SimCh5d, ArrayLitDefaultInit) {
  std::string src =
      "module m;\n"
      "  logic [7:0] arr [0:2] = '{default: 8'h99};\n"
      "endmodule\n";
  SimCh5dFixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0x99);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0x99);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0x99);
}

// §5.11: Index key with default — '{idx:val, default:val}.
TEST(SimCh5d, ArrayLitIndexKeyDefault) {
  std::string src =
      "module m;\n"
      "  logic [7:0] arr [0:2];\n"
      "  initial begin\n"
      "    arr = '{1: 8'hBB, default: 8'h00};\n"
      "  end\n"
      "endmodule\n";
  SimCh5dFixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0x00);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0xBB);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0x00);
}

// §5.11: Index key in declaration initializer.
TEST(SimCh5d, ArrayLitIndexKeyInit) {
  std::string src =
      "module m;\n"
      "  logic [7:0] arr [0:2] = '{2: 8'hCC, default: 8'h11};\n"
      "endmodule\n";
  SimCh5dFixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0x11);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0x11);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0xCC);
}

// §5.11: Descending array range — '{val, val, val} maps left-to-right.
TEST(SimCh5d, ArrayLitDescending) {
  std::string src =
      "module m;\n"
      "  logic [7:0] arr [2:0] = '{8'hAA, 8'hBB, 8'hCC};\n"
      "endmodule\n";
  SimCh5dFixture f;
  auto* design = ElaborateSrc(src, f);
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
TEST(SimCh5d, ArrayLitTypeFromContext) {
  std::string src =
      "module m;\n"
      "  logic [7:0] arr [0:1];\n"
      "  initial begin\n"
      "    arr = '{8'hDE, 8'hAD};\n"
      "  end\n"
      "endmodule\n";
  SimCh5dFixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0xDE);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0xAD);
}

// ===== §5.12 Attributes =====

// §5.12: Attribute on variable declaration (LRM Example 5).
TEST(SimCh5d, AttrOnVarDecl) {
  std::string src =
      "module m;\n"
      "  (* fsm_state *) logic [7:0] x = 8'hAB;\n"
      "endmodule\n";
  SimCh5dFixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("x")->value.ToUint64(), 0xAB);
}

// §5.12: Attribute with explicit value on declaration (LRM Example 5).
TEST(SimCh5d, AttrWithValueOnDecl) {
  std::string src =
      "module m;\n"
      "  (* fsm_state = 1 *) logic [7:0] y = 8'hCD;\n"
      "endmodule\n";
  SimCh5dFixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("y")->value.ToUint64(), 0xCD);
}

// §5.12: Multiple attribute specs in one instance.
TEST(SimCh5d, AttrMultipleSpecs) {
  std::string src =
      "module m;\n"
      "  (* full_case, parallel_case *) logic [7:0] z = 8'hEF;\n"
      "endmodule\n";
  SimCh5dFixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("z")->value.ToUint64(), 0xEF);
}

// §5.12: Multiple separate attribute instances (LRM Example 1 alt).
TEST(SimCh5d, AttrMultipleInstances) {
  std::string src =
      "module m;\n"
      "  (* full_case = 1 *)\n"
      "  (* parallel_case = 1 *)\n"
      "  logic [7:0] w = 8'h77;\n"
      "endmodule\n";
  SimCh5dFixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("w")->value.ToUint64(), 0x77);
}

// §5.12: Attribute on initial block statement.
TEST(SimCh5d, AttrOnInitialBlock) {
  std::string src =
      "module m;\n"
      "  logic [7:0] a;\n"
      "  (* synthesis_off *) initial begin\n"
      "    a = 8'h55;\n"
      "  end\n"
      "endmodule\n";
  SimCh5dFixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 0x55);
}

// §5.12: Attribute on assignment statement inside initial block.
TEST(SimCh5d, AttrOnAssignStmt) {
  std::string src =
      "module m;\n"
      "  logic [7:0] b;\n"
      "  initial begin\n"
      "    (* mark *) b = 8'hDD;\n"
      "  end\n"
      "endmodule\n";
  SimCh5dFixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 0xDD);
}

// §5.12: Attribute on if statement.
TEST(SimCh5d, AttrOnIfStmt) {
  std::string src =
      "module m;\n"
      "  logic [7:0] c;\n"
      "  initial begin\n"
      "    (* high_pri *) if (1) c = 8'hAA;\n"
      "    else c = 8'h00;\n"
      "  end\n"
      "endmodule\n";
  SimCh5dFixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 0xAA);
}

// §5.12: Attribute on case statement (LRM Example 1).
TEST(SimCh5d, AttrOnCaseStmt) {
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
  SimCh5dFixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("d")->value.ToUint64(), 0x22);
}

// §5.12: Attribute on for loop statement.
TEST(SimCh5d, AttrOnForLoop) {
  std::string src =
      "module m;\n"
      "  logic [7:0] e;\n"
      "  initial begin\n"
      "    e = 0;\n"
      "    (* unroll *) for (int i = 0; i < 3; i = i + 1)\n"
      "      e = e + 8'd1;\n"
      "  end\n"
      "endmodule\n";
  SimCh5dFixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("e")->value.ToUint64(), 3);
}

// §5.12: Attribute with string value (LRM Example 6).
TEST(SimCh5d, AttrWithStringValue) {
  std::string src =
      "module m;\n"
      "  (* mode = \"fast\" *) logic [7:0] g = 8'h99;\n"
      "endmodule\n";
  SimCh5dFixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("g")->value.ToUint64(), 0x99);
}

// ===== §5.13 Built-in methods =====

// §5.13: Built-in method call with dot notation and parentheses — arr.size().
TEST(SimCh5d, BuiltinMethodCallWithParens) {
  std::string src =
      "module m;\n"
      "  logic [7:0] arr [0:3];\n"
      "  logic [31:0] s;\n"
      "  initial begin\n"
      "    s = arr.size();\n"
      "  end\n"
      "endmodule\n";
  SimCh5dFixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("s")->value.ToUint64(), 4u);
}

// §5.13: Optional empty parentheses — arr.size (property syntax, no parens).
TEST(SimCh5d, BuiltinMethodNoParens) {
  std::string src =
      "module m;\n"
      "  logic [7:0] arr [0:2];\n"
      "  logic [31:0] s;\n"
      "  initial begin\n"
      "    s = arr.size;\n"
      "  end\n"
      "endmodule\n";
  SimCh5dFixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("s")->value.ToUint64(), 3u);
}

// §5.13: Method result used in an expression — arr.size() + 1.
TEST(SimCh5d, BuiltinMethodInExpr) {
  std::string src =
      "module m;\n"
      "  logic [7:0] arr [0:4];\n"
      "  logic [31:0] r;\n"
      "  initial begin\n"
      "    r = arr.size() + 32'd1;\n"
      "  end\n"
      "endmodule\n";
  SimCh5dFixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("r")->value.ToUint64(), 6u);
}

// §5.13: Built-in method on queue — q.size() returns element count.
TEST(SimCh5d, BuiltinMethodOnQueue) {
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
  SimCh5dFixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("s")->value.ToUint64(), 2u);
}

// §5.13: Built-in method with argument — q.push_back(val) modifies queue.
TEST(SimCh5d, BuiltinMethodWithArg) {
  std::string src =
      "module m;\n"
      "  logic [7:0] q [$];\n"
      "  initial begin\n"
      "    q.push_back(8'h42);\n"
      "    q.push_back(8'h43);\n"
      "    q.push_back(8'h44);\n"
      "  end\n"
      "endmodule\n";
  SimCh5dFixture f;
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
TEST(SimCh5d, BuiltinMethodReduction) {
  std::string src =
      "module m;\n"
      "  logic [7:0] arr [0:2] = '{8'd10, 8'd20, 8'd30};\n"
      "  logic [31:0] total;\n"
      "  initial begin\n"
      "    total = arr.sum();\n"
      "  end\n"
      "endmodule\n";
  SimCh5dFixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("total")->value.ToUint64(), 60u);
}

// §5.13: Mutating built-in method — arr.reverse() reorders elements.
TEST(SimCh5d, BuiltinMethodMutating) {
  std::string src =
      "module m;\n"
      "  logic [7:0] arr [0:2] = '{8'hAA, 8'hBB, 8'hCC};\n"
      "  initial begin\n"
      "    arr.reverse();\n"
      "  end\n"
      "endmodule\n";
  SimCh5dFixture f;
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
TEST(SimCh5d, BuiltinMethodMutatingNoParens) {
  std::string src =
      "module m;\n"
      "  logic [7:0] arr [0:2] = '{8'h11, 8'h22, 8'h33};\n"
      "  initial begin\n"
      "    arr.reverse;\n"
      "  end\n"
      "endmodule\n";
  SimCh5dFixture f;
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
TEST(SimCh5d, BuiltinMethodDynArray) {
  std::string src =
      "module m;\n"
      "  logic [7:0] dyn [] = '{8'hDE, 8'hAD};\n"
      "  logic [31:0] s;\n"
      "  initial begin\n"
      "    s = dyn.size();\n"
      "  end\n"
      "endmodule\n";
  SimCh5dFixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("s")->value.ToUint64(), 2u);
}

// §5.13: Queue pop_front — void mutating method with implicit return.
TEST(SimCh5d, BuiltinMethodQueuePopFront) {
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
  SimCh5dFixture f;
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
