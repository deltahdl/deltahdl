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

struct SimCh506Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign* ElaborateSrc(const std::string& src, SimCh506Fixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

static uint64_t RunAndGet(const std::string& src, const char* var_name) {
  SimCh506Fixture f;
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (!design) return 0;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable(var_name);
  EXPECT_NE(var, nullptr);
  if (!var) return 0;
  return var->value.ToUint64();
}

// ===========================================================================
// §5.6 Identifiers, keywords, and system names
// ===========================================================================

// ---------------------------------------------------------------------------
// 1. Simple identifier with dollar sign ($) in name
// ---------------------------------------------------------------------------
TEST(SimCh506, IdentifierWithDollarSign) {
  // §5.6: Simple identifiers may contain letters, digits, $, and _.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] n$657;\n"
      "  initial n$657 = 8'd42;\n"
      "endmodule\n",
      "n$657");
  EXPECT_EQ(result, 42u);
}

// ---------------------------------------------------------------------------
// 2. Identifier starting with underscore
// ---------------------------------------------------------------------------
TEST(SimCh506, IdentifierStartingWithUnderscore) {
  // §5.6: First character must be a letter or underscore (not digit or $).
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] _bus3;\n"
      "  initial _bus3 = 8'd55;\n"
      "endmodule\n",
      "_bus3");
  EXPECT_EQ(result, 55u);
}

// ---------------------------------------------------------------------------
// 3. Identifiers are case sensitive
// ---------------------------------------------------------------------------
TEST(SimCh506, IdentifiersCaseSensitive) {
  // §5.6: Identifiers are case sensitive.
  SimCh506Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] data, Data, DATA;\n"
      "  initial begin\n"
      "    data = 8'd10;\n"
      "    Data = 8'd20;\n"
      "    DATA = 8'd30;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* v1 = f.ctx.FindVariable("data");
  auto* v2 = f.ctx.FindVariable("Data");
  auto* v3 = f.ctx.FindVariable("DATA");
  ASSERT_NE(v1, nullptr);
  ASSERT_NE(v2, nullptr);
  ASSERT_NE(v3, nullptr);
  EXPECT_EQ(v1->value.ToUint64(), 10u);
  EXPECT_EQ(v2->value.ToUint64(), 20u);
  EXPECT_EQ(v3->value.ToUint64(), 30u);
}

// ---------------------------------------------------------------------------
// 4. Long identifier (1024 characters — the minimum required maximum)
// ---------------------------------------------------------------------------
TEST(SimCh506, LongIdentifier1024Chars) {
  // §5.6: Maximum identifier length is at least 1024 characters.
  std::string long_id(1024, 'a');
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] " +
          long_id +
          ";\n"
          "  initial " +
          long_id +
          " = 8'd77;\n"
          "endmodule\n",
      long_id.c_str());
  EXPECT_EQ(result, 77u);
}

// ---------------------------------------------------------------------------
// 5. Identifier with digits (not as first character)
// ---------------------------------------------------------------------------
TEST(SimCh506, IdentifierWithDigits) {
  // §5.6: Simple identifiers can contain digits (not as first character).
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] abc123;\n"
      "  initial abc123 = 8'd88;\n"
      "endmodule\n",
      "abc123");
  EXPECT_EQ(result, 88u);
}

// ---------------------------------------------------------------------------
// 6. Identifier references an object by name
// ---------------------------------------------------------------------------
TEST(SimCh506, IdentifierReferencesObject) {
  // §5.6: An identifier gives an object a unique name for referencing.
  SimCh506Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] source, sink;\n"
      "  initial begin\n"
      "    source = 8'd66;\n"
      "    sink = source;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("sink");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 66u);
}

// ---------------------------------------------------------------------------
// 7. Multiple identifiers with mixed character classes
// ---------------------------------------------------------------------------
TEST(SimCh506, IdentifierMixedCharClasses) {
  // §5.6: Identifiers use letters, digits, $, _ in combination.
  SimCh506Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] _start, mid$dle, end_99, result;\n"
      "  initial begin\n"
      "    _start = 8'd1;\n"
      "    mid$dle = 8'd2;\n"
      "    end_99 = 8'd3;\n"
      "    result = _start + mid$dle + end_99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 6u);
}
