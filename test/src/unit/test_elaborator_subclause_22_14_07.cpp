#include <gtest/gtest.h>

#include <string>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_included_keyword_elab.h"
#include "helpers_keyword_version.h"
#include "helpers_reported_error.h"
#include "helpers_reserved_keyword_elab.h"
#include "helpers_rtlir_lookup.h"
#include "model_keyword_table_sweeps.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {
TEST(SystemVerilog2009KeywordElaboration, IncludedVerilog1995WordsAreReserved) {
  ExpectKeywordTableIsReserved("1800-2009", kVerilog1995KeywordSweep);
}

TEST(SystemVerilog2009KeywordElaboration, IncludedVerilog2001WordsAreReserved) {
  ExpectKeywordTableIsReserved("1800-2009", kVerilog2001AddedKeywordSweep);
  ExpectConfigurationWordsNameVariablesUnderNoconfig();
}

TEST(SystemVerilog2009KeywordElaboration, IncludedVerilog2005WordIsReserved) {
  ExpectKeywordTableIsReserved("1800-2009", kVerilog2005AddedKeywordSweep);
  ExpectVerilog2005DeclarationsElaborate("1800-2009");
}

TEST(SystemVerilog2009KeywordElaboration,
     IncludedSystemVerilog2005WordsAreReserved) {
  ExpectKeywordTableIsReserved("1800-2009",
                               kSystemVerilog2005AddedKeywordSweep);
}

TEST(SystemVerilog2009KeywordElaboration, AddedWordsCannotNameVariables) {
  ExpectKeywordTableIsReserved("1800-2009",
                               kSystemVerilog2009AddedKeywordSweep);
}

TEST(SystemVerilog2009KeywordElaboration, AddedLetDeclarationsReachTheDesign) {
  const std::string kSrc =
      "let gain = 21;\n"
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] r;\n"
      "  let sum(untyped x, int y) = x + y;\n"
      "  initial r = sum(a, gain);\n"
      "endmodule\n";

  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(InSv2009(kSrc), f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  ExpectLetDeclarationsElaborated(design);

  ElabFixture included;
  ElaborateWithPreprocessorAllowingParseErrors(InSv2005(kSrc), included, "m");
  EXPECT_TRUE(ReportedError(included.diag.Diagnostics(),
                            "expected top-level declaration", LineInRegion(1),
                            "3.12.1"));
}

TEST(SystemVerilog2009KeywordElaboration, AddedCheckerElementIsInstantiable) {
  const std::string kSrc =
      "checker handshake (logic clk, logic req);\n"
      "  assert property (@(posedge clk) req);\n"
      "endchecker\n"
      "module m;\n"
      "  logic clk;\n"
      "  logic req;\n"
      "  handshake u_chk (clk, req);\n"
      "endmodule\n";

  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(InSv2009(kSrc), f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* m = FindModule(design, "m");
  ASSERT_NE(m, nullptr);
  bool instance_seen = false;
  for (const auto& child : m->children) {
    if (child.inst_name == "u_chk") {
      EXPECT_EQ(child.module_name, "handshake");
      instance_seen = true;
    }
  }
  EXPECT_TRUE(instance_seen);

  ElabFixture included;
  ElaborateWithPreprocessorAllowingParseErrors(InSv2005(kSrc), included, "m");
  EXPECT_TRUE(ReportedError(included.diag.Diagnostics(),
                            "expected top-level declaration", LineInRegion(1),
                            "3.12.1"));
}

TEST(SystemVerilog2009KeywordElaboration,
     AddedGlobalClockingIsCountedAtElaboration) {
  const std::string kOne =
      "module m (input logic clk);\n"
      "  global clocking gcb @(posedge clk); endclocking\n"
      "  clocking cb @(posedge clk); input clk; endclocking\n"
      "endmodule\n";
  ElabFixture one;
  auto* design = ElaborateWithPreprocessor(InSv2009(kOne), one, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(one.has_errors);

  ElabFixture two;
  ElaborateWithPreprocessor(
      InSv2009("module m (input logic clk);\n"
               "  global clocking gcb  @(posedge clk); endclocking\n"
               "  global clocking gcb2 @(negedge clk); endclocking\n"
               "endmodule\n"),
      two, "m");
  EXPECT_TRUE(ReportedError(two.diag.Diagnostics(),
                            "only one global clocking block is allowed per "
                            "scope",
                            LineInRegion(3), "14.14"));

  const std::string kReference =
      "module m (input logic clk, input logic a);\n"
      "  global clocking gcb @(posedge clk); endclocking\n"
      "  assert property (@($global_clock) a);\n"
      "endmodule\n";
  ElabFixture with_block;
  design = ElaborateWithPreprocessor(InSv2009(kReference), with_block, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(with_block.has_errors);

  ElabFixture without_block;
  ElaborateWithPreprocessor(
      InSv2009("module m (input logic clk, input logic a);\n"
               "  assert property (@($global_clock) a);\n"
               "endmodule\n"),
      without_block, "m");
  EXPECT_TRUE(ReportedError(
      without_block.diag.Diagnostics(),
      "$global_clock has no effective global clocking declaration",
      LineInRegion(2), "14.14"));

  for (const auto& src : {kOne, kReference}) {
    ElabFixture included;
    ElaborateWithPreprocessorAllowingParseErrors(InSv2005(src), included, "m");
    EXPECT_TRUE(ReportedError(included.diag.Diagnostics(),
                              "expected ';', got 'clocking'", LineInRegion(2),
                              "6.8"))
        << src;
  }
}

TEST(SystemVerilog2009KeywordElaboration,
     AddedQualifierAndRestrictConstructsReachTheDesign) {
  const std::string kSrc =
      "module m (input logic clk, input logic req);\n"
      "  logic [1:0] sel;\n"
      "  logic [7:0] r;\n"
      "  restrict property (@(posedge clk) req);\n"
      "  assert property (@(posedge clk) req);\n"
      "  initial begin\n"
      "    sel = 2'b01;\n"
      "    unique0 case (sel) 2'b01: r = 8'd1; default: r = 8'd0; endcase\n"
      "  end\n"
      "endmodule\n";

  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(InSv2009(kSrc), f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* m = FindModule(design, "m");
  ASSERT_NE(m, nullptr);
  bool qualified_case_seen = false;
  for (const auto& proc : m->processes) {
    if (proc.kind != RtlirProcessKind::kInitial || proc.body == nullptr)
      continue;
    for (auto* s : proc.body->stmts) {
      if (s != nullptr && s->kind == StmtKind::kCase) {
        EXPECT_EQ(s->qualifier, CaseQualifier::kUnique0);
        qualified_case_seen = true;
      }
    }
  }
  EXPECT_TRUE(qualified_case_seen);

  ElabFixture included;
  ElaborateWithPreprocessorAllowingParseErrors(InSv2005(kSrc), included, "m");
  EXPECT_TRUE(ReportedError(included.diag.Diagnostics(),
                            "expected ';', got 'property'", LineInRegion(4),
                            "6.8"));
}

TEST(SystemVerilog2009KeywordElaboration,
     IncludedVerilog1995WordsStillBuildDesign) {
  ExpectVerilog1995DeclarationsElaborate("1800-2009");
}

TEST(SystemVerilog2009KeywordElaboration,
     IncludedVerilog2001WordsStillBuildDesign) {
  ExpectVerilog2001DeclarationsElaborate("1800-2009");
}

TEST(SystemVerilog2009KeywordElaboration,
     IncludedSystemVerilog2005WordsStillBuildDesign) {
  ExpectSystemVerilog2005DeclarationsElaborate("1800-2009");
}

TEST(SystemVerilog2009KeywordElaboration,
     EveryConstantFormResolvesUnderThisVersion) {
  ExpectEveryConstantFormResolves("1800-2009", "int ", "byte");
}

TEST(SystemVerilog2009KeywordElaboration, EveryDeclarationFormStillElaborates) {
  ExpectEveryDeclarationFormElaborates("1800-2009");
}

TEST(SystemVerilog2009KeywordElaboration, LaterWordsNameObjectsButAreNotTypes) {
  ExpectWordsNameObjectsButAreNotTypes(
      "1800-2009", {"implements", "interconnect", "nettype", "soft"},
      "1800-2012");
}

}  // namespace
