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

struct SimCh510Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign *ElaborateSrc(const std::string &src, SimCh510Fixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

static uint64_t RunAndGet(const std::string &src, const char *var_name) {
  SimCh510Fixture f;
  auto *design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (!design)
    return 0;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable(var_name);
  EXPECT_NE(var, nullptr);
  if (!var)
    return 0;
  return var->value.ToUint64();
}

// ===========================================================================
// §5.10 Structure literals
// ===========================================================================

// ---------------------------------------------------------------------------
// 1. Positional assignment pattern — type from left-hand context
// ---------------------------------------------------------------------------
TEST(SimCh510, StructLitPositional) {
  // §5.10: c = '{0, 0.0}; — type from left-hand context (packed struct).
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
      "  ab_t c;\n"
      "  initial c = '{8'hAA, 8'hBB};\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0xAABBu);
}

// ---------------------------------------------------------------------------
// 2. Member name and value — §5.10 / §10.9.2
// ---------------------------------------------------------------------------
TEST(SimCh510, StructLitMemberName) {
  // §5.10: c = '{a:0, b:0.0};  — member name and value for that member
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
      "  ab_t c;\n"
      "  initial c = '{a: 8'h11, b: 8'h22};\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x1122u);
}

// ---------------------------------------------------------------------------
// 3. Default value — all elements set to same value
// ---------------------------------------------------------------------------
TEST(SimCh510, StructLitDefault) {
  // §5.10: c = '{default:0};  — all elements of structure c are set to 0
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
      "  ab_t c;\n"
      "  initial c = '{default: 8'hFF};\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0xFFFFu);
}

// ---------------------------------------------------------------------------
// 4. Member name and value — reverse order
// ---------------------------------------------------------------------------
TEST(SimCh510, StructLitMemberNameReverse) {
  // §5.10 / §10.9.2: Named patterns can be in any order.
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
      "  ab_t c;\n"
      "  initial c = '{b: 8'h22, a: 8'h11};\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x1122u);
}

// ---------------------------------------------------------------------------
// 5. Struct literal in variable initialization
// ---------------------------------------------------------------------------
TEST(SimCh510, StructLitVarInit) {
  // §5.10: Structure literal used in variable declaration initializer.
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] x; logic [7:0] y; } pt_t;\n"
      "  pt_t p = '{x: 8'hAA, y: 8'hBB};\n"
      "endmodule\n",
      "p");
  EXPECT_EQ(v, 0xAABBu);
}

// ---------------------------------------------------------------------------
// 6. Default value with different-width fields
// ---------------------------------------------------------------------------
TEST(SimCh510, StructLitDefaultDiffWidth) {
  // §5.10: '{default:val} applies to all fields; each truncates to width.
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [3:0] b; } ab_t;\n"
      "  ab_t c;\n"
      "  initial c = '{default: '1};\n"
      "endmodule\n",
      "c");
  // a = 8'hFF (bits 11:4), b = 4'hF (bits 3:0) → 0xFFF
  EXPECT_EQ(v, 0xFFFu);
}

// ---------------------------------------------------------------------------
// 7. Positional pattern with three fields
// ---------------------------------------------------------------------------
TEST(SimCh510, StructLitPositionalThree) {
  // §5.10: Positional assignment with 3 fields.
  auto v = RunAndGet("module t;\n"
                     "  typedef struct packed {\n"
                     "    logic [7:0] a; logic [7:0] b; logic [7:0] c;\n"
                     "  } abc_t;\n"
                     "  abc_t s;\n"
                     "  initial s = '{8'h11, 8'h22, 8'h33};\n"
                     "endmodule\n",
                     "s");
  EXPECT_EQ(v, 0x112233u);
}

// ---------------------------------------------------------------------------
// 8. Struct field access after literal assignment
// ---------------------------------------------------------------------------
TEST(SimCh510, StructLitFieldAccess) {
  // §5.10: After assigning via struct literal, individual fields are readable.
  SimCh510Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] x; logic [7:0] y; } pt_t;\n"
      "  pt_t p;\n"
      "  logic [7:0] rx, ry;\n"
      "  initial begin\n"
      "    p = '{x: 8'hDE, y: 8'hAD};\n"
      "    rx = p.x;\n"
      "    ry = p.y;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(design, nullptr);
  if (!design)
    return;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *vrx = f.ctx.FindVariable("rx");
  auto *vry = f.ctx.FindVariable("ry");
  EXPECT_NE(vrx, nullptr);
  EXPECT_NE(vry, nullptr);
  if (!vrx || !vry)
    return;
  EXPECT_EQ(vrx->value.ToUint64(), 0xDEu);
  EXPECT_EQ(vry->value.ToUint64(), 0xADu);
}

// ---------------------------------------------------------------------------
// 9. Default value with zero — all fields cleared
// ---------------------------------------------------------------------------
TEST(SimCh510, StructLitDefaultZero) {
  // §5.10 LRM example: c = '{default:0};
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
      "  ab_t c;\n"
      "  initial c = '{default: 0};\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0u);
}

// ---------------------------------------------------------------------------
// 10. Positional pattern — type from init context (declaration)
// ---------------------------------------------------------------------------
TEST(SimCh510, StructLitPositionalInit) {
  // §5.10: Structure literal type from declaration context.
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
      "  ab_t c = '{8'h55, 8'hAA};\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x55AAu);
}
