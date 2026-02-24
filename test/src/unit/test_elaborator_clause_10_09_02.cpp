// §10.9.2: Structure assignment patterns

#include <gtest/gtest.h>
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

struct ElabA60701Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign *ElaborateSrc(const std::string &src, ElabA60701Fixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

namespace {

// =============================================================================
// A.6.7.1 Patterns — Elaboration tests
// =============================================================================
// §10.9: positional assignment pattern elaborates for struct init
TEST(ElabA60701, StructPositionalPatternElaborates) {
  ElabA60701Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = '{8'd10, 8'd20};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

// =============================================================================
// Helper fixture
// =============================================================================
struct AggFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static Expr *ParseExprFrom(const std::string &src, AggFixture &f) {
  std::string code = "module t; initial x = " + src + "; endmodule";
  auto fid = f.mgr.AddFile("<test>", code);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  auto *item = cu->modules[0]->items[0];
  return item->body->rhs;
}

static Expr *MakeIntLit(Arena &arena, uint64_t val) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = val;
  return e;
}

TEST(StructPattern, MixedPrecedence) {
  // '{a: 1, byte: 2, default: 3} — member > type > default
  // struct { byte a; byte b; logic [7:0] c; }
  // a=1 (explicit member overrides byte key), b=2 (byte type key), c=3
  // (default)
  AggFixture f;
  StructTypeInfo info;
  info.type_name = "multi_t";
  info.is_packed = true;
  info.total_width = 24;
  info.fields.push_back({"a", 16, 8, DataTypeKind::kByte});
  info.fields.push_back({"b", 8, 8, DataTypeKind::kByte});
  info.fields.push_back({"c", 0, 8, DataTypeKind::kLogic});

  auto *pat = f.arena.Create<Expr>();
  pat->kind = ExprKind::kAssignmentPattern;
  pat->pattern_keys = {"a", "byte", "default"};
  pat->elements = {MakeIntLit(f.arena, 1), MakeIntLit(f.arena, 2),
                   MakeIntLit(f.arena, 3)};

  auto result = EvalStructPattern(pat, &info, f.ctx, f.arena);
  uint64_t expected = (uint64_t{1} << 16) | (uint64_t{2} << 8) | 3;
  EXPECT_EQ(result.ToUint64(), expected);
}

// §10.9: typed assignment pattern expression elaborates
TEST(ElabA60701, TypedPatternExpressionElaborates) {
  ElabA60701Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] x; logic [7:0] y; } coord_t;\n"
      "  coord_t c;\n"
      "  initial begin\n"
      "    c = coord_t'{x: 8'd5, y: 8'd10};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

}  // namespace
