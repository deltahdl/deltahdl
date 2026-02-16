// Tests for LRM section 39.4.1, 39.4.2, 39.5.2 -- Assertion API system
// functions and assertion control

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult39 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult39 Parse(const std::string& src) {
  ParseResult39 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static bool ParseOk(const std::string& src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

// =============================================================================
// LRM section 39.4.1 -- Placing assertion system callbacks
// These system tasks control assertion processing at the system level:
// $assertOn, $assertOff, $assertKill
// =============================================================================

TEST(ParserSection39, AssertOnNoArgs) {
  // $assertOn with no arguments enables all assertions
  auto r = Parse(R"(
    module m;
      initial $asserton;
    endmodule
  )");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserSection39, AssertOffNoArgs) {
  // $assertOff with no arguments disables all assertions
  auto r = Parse(R"(
    module m;
      initial $assertoff;
    endmodule
  )");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserSection39, AssertKillNoArgs) {
  // $assertKill kills all active assertion attempts
  auto r = Parse(R"(
    module m;
      initial $assertkill;
    endmodule
  )");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserSection39, AssertOnWithLevelArg) {
  // $asserton with levels_arg controls depth of hierarchy
  EXPECT_TRUE(ParseOk(R"(
    module m;
      initial $asserton(0);
    endmodule
  )"));
}

TEST(ParserSection39, AssertOffWithLevelAndModuleArgs) {
  // $assertoff with levels and list of modules/instances
  EXPECT_TRUE(ParseOk(R"(
    module m;
      initial $assertoff(0, m);
    endmodule
  )"));
}

// =============================================================================
// LRM section 39.4.2 -- Placing assertion callbacks
// These tests verify assertion-related syntax that enables placement of
// callbacks on assertion statements (assert, assume, cover properties).
// =============================================================================

TEST(ParserSection39, AssertPropertyStatement) {
  // assert property is the target of assertion callbacks
  auto r = Parse(R"(
    module m;
      logic clk, a, b;
      assert property (@(posedge clk) a |-> b);
    endmodule
  )");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  // Find the assert property item
  bool found_assert = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAssertProperty) {
      found_assert = true;
    }
  }
  EXPECT_TRUE(found_assert);
}

TEST(ParserSection39, AssumePropertyStatement) {
  // assume property can also have callbacks placed on it
  EXPECT_TRUE(ParseOk(R"(
    module m;
      logic clk, req, gnt;
      assume property (@(posedge clk) req |-> ##[1:3] gnt);
    endmodule
  )"));
}

TEST(ParserSection39, CoverPropertyStatement) {
  // cover property is used for coverage callbacks
  EXPECT_TRUE(ParseOk(R"(
    module m;
      logic clk, a, b;
      cover property (@(posedge clk) a ##1 b);
    endmodule
  )"));
}

TEST(ParserSection39, AssertPropertyWithActionBlocks) {
  // Assert property with pass and fail action blocks
  EXPECT_TRUE(ParseOk(R"(
    module m;
      logic clk, a, b;
      assert property (@(posedge clk) a |-> b)
        $display("pass")
      else
        $error("fail");
    endmodule
  )"));
}

TEST(ParserSection39, MultipleAssertionStatements) {
  // Multiple assertion statements that can independently have callbacks
  EXPECT_TRUE(ParseOk(R"(
    module m;
      logic clk, a, b, c;
      a1: assert property (@(posedge clk) a |-> b);
      a2: assert property (@(posedge clk) b |-> c);
      c1: cover property (@(posedge clk) a ##1 b ##1 c);
    endmodule
  )"));
}

// =============================================================================
// LRM section 39.5.2 -- Assertion control via system tasks
// The assertion control functions $assertcontrol and related tasks allow
// runtime control over assertion evaluation.
// =============================================================================

TEST(ParserSection39, AssertControlSystemTask) {
  // $assertcontrol enables runtime assertion control
  EXPECT_TRUE(ParseOk(R"(
    module m;
      initial $assertcontrol(3);
    endmodule
  )"));
}

TEST(ParserSection39, AssertControlWithMultipleArgs) {
  // $assertcontrol with control_type and assertion_type arguments
  EXPECT_TRUE(ParseOk(R"(
    module m;
      initial $assertcontrol(3, 1);
    endmodule
  )"));
}

TEST(ParserSection39, AssertPassStepAndFailStep) {
  // $assertpasson / $assertpassoff control pass action execution
  EXPECT_TRUE(ParseOk(R"(
    module m;
      initial begin
        $assertpasson;
        $assertpassoff;
      end
    endmodule
  )"));
}

TEST(ParserSection39, AssertionControlInAlwaysBlock) {
  // Assertion control tasks in always blocks
  EXPECT_TRUE(ParseOk(R"(
    module m;
      logic clk, reset;
      always @(posedge clk) begin
        if (reset)
          $assertoff(0, m);
        else
          $asserton(0, m);
      end
    endmodule
  )"));
}

TEST(ParserSection39, AssertionControlSequence) {
  // Complete assertion control sequence: off, kill, on
  EXPECT_TRUE(ParseOk(R"(
    module m;
      initial begin
        $assertoff;
        $assertkill;
        #100;
        $asserton;
      end
    endmodule
  )"));
}
