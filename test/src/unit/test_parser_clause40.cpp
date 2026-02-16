// Tests for LRM section 40.5.2 -- Coverage API: obtaining coverage information
// These tests verify that coverage-related system function calls and
// covergroup declarations parse correctly.

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult40 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult40 Parse(const std::string& src) {
  ParseResult40 result;
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
// LRM section 40.5.2 -- Obtaining coverage information
// $coverage_control, $coverage_get_max, $coverage_get, $coverage_merge,
// $coverage_save system functions
// =============================================================================

TEST(ParserSection40, CoverageControlSystemCall) {
  // $coverage_control(control_constant, coverage_type, scope_def,
  // modules_or_instance)
  auto r = Parse(R"(
    module m;
      initial $coverage_control(1, 2, 3);
    endmodule
  )");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserSection40, CoverageGetMaxSystemCall) {
  // $coverage_get_max returns max coverage count
  auto r = Parse(R"(
    module m;
      initial begin
        int x;
        x = $coverage_get_max(0, 0);
      end
    endmodule
  )");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserSection40, CoverageGetSystemCall) {
  // $coverage_get returns current coverage count
  EXPECT_TRUE(ParseOk(R"(
    module m;
      initial begin
        int val;
        val = $coverage_get(0, 0);
      end
    endmodule
  )"));
}

TEST(ParserSection40, CoverageMergeSystemCall) {
  // $coverage_merge merges coverage databases
  EXPECT_TRUE(ParseOk(R"(
    module m;
      initial $coverage_merge("database.ucdb");
    endmodule
  )"));
}

TEST(ParserSection40, CoverageSaveSystemCall) {
  // $coverage_save saves coverage data to file
  EXPECT_TRUE(ParseOk(R"(
    module m;
      initial $coverage_save("coverage.ucdb");
    endmodule
  )"));
}

// =============================================================================
// LRM section 40.5.2 -- Coverage with assertion and covergroup constructs
// The VPI coverage API queries are applied to assertion handles and
// covergroup instances. These tests verify the parser handles the
// constructs that coverage queries operate on.
// =============================================================================

TEST(ParserSection40, CovergroupWithCoverpoint) {
  // Covergroup with coverpoint -- target of vpi_get(vpiCovered, ...)
  EXPECT_TRUE(ParseOk(R"(
    module m;
      logic [2:0] addr;
      covergroup cg @(addr);
        coverpoint addr;
      endgroup
    endmodule
  )"));
}

TEST(ParserSection40, CovergroupWithBins) {
  // Coverpoint with bins -- coverage entities returned by API
  EXPECT_TRUE(ParseOk(R"(
    module m;
      logic [7:0] data;
      covergroup cg @(data);
        coverpoint data {
          bins low = {[0:63]};
          bins mid = {[64:127]};
          bins high = {[128:255]};
        }
      endgroup
    endmodule
  )"));
}

TEST(ParserSection40, CoverPropertyForAssertionCoverage) {
  // cover property -- target of vpiAssertAttemptCovered/vpiAssertSuccessCovered
  EXPECT_TRUE(ParseOk(R"(
    module m;
      logic clk, a, b;
      cover property (@(posedge clk) a |-> ##[1:3] b);
    endmodule
  )"));
}

TEST(ParserSection40, CoverageControlInAlwaysBlock) {
  // Coverage control calls within procedural context
  EXPECT_TRUE(ParseOk(R"(
    module m;
      logic clk, reset;
      always @(posedge clk) begin
        if (reset) begin
          $coverage_control(2, 0, 0);
        end
      end
    endmodule
  )"));
}
