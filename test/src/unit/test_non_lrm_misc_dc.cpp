// Non-LRM tests

#include "fixture_program.h"
#include "fixture_simulator.h"

using namespace delta;

using DpiParseTest = ProgramTestParse;

using ApiParseTest = ProgramTestParse;

static bool ParseOk38(const std::string& src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

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

namespace {

TEST(ParserSection38, MultipleDpiDeclarationsForVpiRegistration) {
  // Multiple import/export declarations modeling a complete VPI registration
  // set
  EXPECT_TRUE(ParseOk38(R"(
    module m;
      import "DPI-C" context function int calltf(input string data);
      import "DPI-C" context function int compiletf(input string data);
      import "DPI-C" pure function int sizetf(input string data);
      export "DPI-C" function sv_calltf_impl;
      export "DPI-C" task sv_task_impl;
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

// §10.9: named assignment pattern elaborates for struct init
TEST(ElabA60701, StructNamedPatternElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = pair_t'{a: 8'd1, b: 8'd2};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

// Clocking block with assertion_item_declaration elaborates
TEST(ElabA611, AssertionItemDeclElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "    property p;\n"
      "      data;\n"
      "    endproperty\n"
      "    sequence s;\n"
      "      data;\n"
      "    endsequence\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
