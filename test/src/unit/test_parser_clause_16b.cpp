#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- Test helpers ---

struct ParseResult16b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static ParseResult16b Parse(const std::string &src) {
  ParseResult16b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =============================================================================
// §16.9 -- System functions for assertions ($sampled, $rose, $fell, $stable)
// =============================================================================

TEST(ParserSection16, SampledFunctionInAssert) {
  auto r = Parse("module m;\n"
                 "  assert property (@(posedge clk) a |-> b)\n"
                 "    else $error(\"a=%b b=%b\", $sampled(a), $sampled(b));\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection16, RoseFunctionInProperty) {
  auto r =
      Parse("module m;\n"
            "  assert property (@(posedge clk) $rose(req) |-> ##[1:3] ack);\n"
            "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection16, FellFunctionInProperty) {
  auto r = Parse("module m;\n"
                 "  assert property (@(posedge clk) $fell(req) |-> ##1 !ack);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection16, StableFunctionInProperty) {
  auto r = Parse("module m;\n"
                 "  assert property (@(posedge clk) $stable(data) |-> valid);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection16, PastFunctionWithTicks) {
  auto r = Parse("module m;\n"
                 "  assert property (@(posedge clk) $past(req, 2) |-> ack);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection16, ChangedFunctionInProperty) {
  auto r =
      Parse("module m;\n"
            "  assert property (@(posedge clk) $changed(data) |-> valid);\n"
            "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// §16.12 -- Declaring sequences (additional tests)
// =============================================================================

TEST(ParserSection16, SequenceWithRangeDelay) {
  auto r = Parse("module m;\n"
                 "  sequence s_handshake;\n"
                 "    req ##[1:5] ack;\n"
                 "  endsequence\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool found = false;
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kSequenceDecl) {
      found = true;
      EXPECT_EQ(item->name, "s_handshake");
    }
  }
  EXPECT_TRUE(found);
}

TEST(ParserSection16, SequenceWithFormalArgsDecl) {
  auto r = Parse("module m;\n"
                 "  sequence s_req_ack(req, ack);\n"
                 "    req ##1 ack;\n"
                 "  endsequence\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection16, SequenceUsedInPropertyDecl) {
  auto r = Parse("module m;\n"
                 "  sequence s1;\n"
                 "    a ##1 b;\n"
                 "  endsequence\n"
                 "  property p1;\n"
                 "    @(posedge clk) s1 |=> c;\n"
                 "  endproperty\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// §16.14 -- Declaring properties (additional tests)
// =============================================================================

TEST(ParserSection16, PropertyWithDisableIffDecl) {
  auto r = Parse("module m;\n"
                 "  property p_req_ack;\n"
                 "    @(posedge clk) disable iff (rst)\n"
                 "    req |-> ##[1:3] ack;\n"
                 "  endproperty\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection16, PropertyWithFormalArgsDecl) {
  auto r = Parse("module m;\n"
                 "  property p_valid(signal, valid);\n"
                 "    @(posedge clk) signal |-> valid;\n"
                 "  endproperty\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection16, PropertyDeclWithEndLabel) {
  auto r = Parse("module m;\n"
                 "  property p1;\n"
                 "    @(posedge clk) a |-> b;\n"
                 "  endproperty : p1\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// §16.14.6.2 -- Multiclock support
// =============================================================================

TEST(ParserSection16, MultichannelAssertPropertyInline) {
  auto r = Parse("module m;\n"
                 "  assert property (\n"
                 "    @(posedge clk1) a ##1 @(posedge clk2) b\n"
                 "  );\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection16, MulticlockPropertyDeclImplication) {
  auto r = Parse("module m;\n"
                 "  property p_multi;\n"
                 "    @(posedge clk1) req |=> @(posedge clk2) ack;\n"
                 "  endproperty\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection16, MulticlockSequenceDeclTwo) {
  auto r = Parse("module m;\n"
                 "  sequence s_multi;\n"
                 "    @(posedge clk1) a ##1 @(posedge clk2) b;\n"
                 "  endsequence\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// §16.14.7 -- Inferred clocking and disable functions
// =============================================================================

TEST(ParserSection16, InferredClockInProperty) {
  auto r = Parse("module m;\n"
                 "  default clocking @(posedge clk); endclocking\n"
                 "  property p_inferred(clk_ev = $inferred_clock);\n"
                 "    @clk_ev a |-> b;\n"
                 "  endproperty\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection16, InferredDisableInProperty) {
  auto r = Parse("module m;\n"
                 "  default disable iff rst;\n"
                 "  property p_dis(rst_cond = $inferred_disable);\n"
                 "    disable iff (rst_cond) a |-> b;\n"
                 "  endproperty\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection16, InferredClockAndDisableTogether) {
  auto r =
      Parse("module m;\n"
            "  default clocking @(negedge clk); endclocking\n"
            "  default disable iff rst;\n"
            "  property p_both(c = $inferred_clock, d = $inferred_disable);\n"
            "    @c disable iff (d) req |-> ack;\n"
            "  endproperty\n"
            "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// §16.9.4 -- Sequence throughout (additional tests)
// =============================================================================

TEST(ParserSection16, SequenceThroughoutWithImplication) {
  auto r = Parse("module m;\n"
                 "  assert property (\n"
                 "    @(posedge clk) req |-> en throughout (##2 ack[*3]));\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// §16.14.6 -- Property case (additional tests)
// =============================================================================

TEST(ParserSection16, PropertyCaseWithDefaultOnly) {
  auto r = Parse("module m;\n"
                 "  property p_mode;\n"
                 "    case (mode)\n"
                 "      default: a |-> b;\n"
                 "    endcase\n"
                 "  endproperty\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}
