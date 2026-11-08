#include <gtest/gtest.h>

#include <cstddef>
#include <iterator>
#include <string>

#include "fixture_parser.h"
#include "helpers_identifier_position_sweep.h"
#include "helpers_included_keyword_parse.h"
#include "helpers_keyword_version.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "model_keyword_table_sweeps.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {
TEST(CompilerDirectiveParsing,
     SystemVerilog2009ReservesEveryVerilog1995Keyword) {
  ExpectKeywordTableIsReservedAtParse("1800-2009",
                                      kVerilog1995KeywordSweepAtParse);
}

TEST(CompilerDirectiveParsing,
     SystemVerilog2009ReservesEveryVerilog2001Keyword) {
  ExpectKeywordTableIsReservedAtParse("1800-2009",
                                      kVerilog2001AddedKeywordSweep);
  ExpectConfigurationWordsNameVariablesAtParse();
}

TEST(CompilerDirectiveParsing, SystemVerilog2009ReservesTheVerilog2005Word) {
  ExpectKeywordTableIsReservedAtParse("1800-2009",
                                      kVerilog2005AddedKeywordSweep);
  ExpectUwireStillOpensNetDeclarations("1800-2009");
}

TEST(CompilerDirectiveParsing,
     SystemVerilog2009ReservesEverySystemVerilog2005Keyword) {
  ExpectKeywordTableIsReservedAtParse("1800-2009",
                                      kSystemVerilog2005AddedKeywordSweep);
}

TEST(CompilerDirectiveParsing, SystemVerilog2009ReservesEveryWordItAdds) {
  ExpectKeywordTableIsReservedAtParse("1800-2009",
                                      kSystemVerilog2009AddedKeywordSweep);
}

TEST(CompilerDirectiveParsing,
     SystemVerilog2009ReservedWordsFillNoIdentifierPosition) {
  ExpectWordsFillNoIdentifierPosition(
      "1800-2009", {"wire", "generate", "uwire", "logic"},
      {"design element", "port", "instance", "task", "named block"});
}

TEST(CompilerDirectiveParsing,
     SystemVerilog2009AddedWordsNameEntitiesUnderIncludedLists) {
  ExpectWordsNameEntitiesUnder("1800-2005", "1800-2009",
                               {"until", "weak", "unique0"});

  auto named_module =
      ParseWithPreprocessor(InSv2005("module until;\nendmodule\n"));
  ASSERT_NE(named_module.cu, nullptr);
  ASSERT_EQ(named_module.cu->modules.size(), 1u);
  EXPECT_EQ(named_module.cu->modules[0]->name, "until");

  auto named_gate =
      ParseWithPreprocessor(InSv2005("module m (input wire a, output wire y);\n"
                                     "  and weak (y, a, a);\n"
                                     "endmodule\n"));
  ASSERT_NE(named_gate.cu, nullptr);
  auto* gate = FindGateByKind(named_gate.cu->modules[0]->items, GateKind::kAnd);
  ASSERT_NE(gate, nullptr);
  EXPECT_EQ(gate->gate_inst_name, "weak");
}

TEST(CompilerDirectiveParsing, SystemVerilog2009AddedCheckerOpensAnElement) {
  const std::string kSrc =
      "checker handshake (logic clk, logic req);\n"
      "  assert property (@(posedge clk) req);\n"
      "endchecker\n"
      "module m;\n"
      "  logic clk;\n"
      "  logic req;\n"
      "  handshake u_chk (clk, req);\n"
      "endmodule\n";

  auto r = ParseWithPreprocessor(InSv2009(kSrc));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->name, "handshake");
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");

  auto before = ParseWithPreprocessor(InSv2005(kSrc));
  EXPECT_TRUE(ReportedError(before.diags, "expected top-level declaration",
                            LineInRegion(1), "3.12.1"));
}

TEST(CompilerDirectiveParsing, SystemVerilog2009AddedLetOpensDeclarations) {
  const std::string kSrc =
      "let gain = 21;\n"
      "module m (input logic clk);\n"
      "  logic [7:0] a, b, r;\n"
      "  let sum(untyped x, int y) = x + y;\n"
      "  clocking cb @(posedge clk);\n"
      "    let half = 4;\n"
      "  endclocking\n"
      "  initial begin\n"
      "    let inner(untyped z) = z + z;\n"
      "    r = inner(a) + sum(a, b) + gain;\n"
      "  end\n"
      "endmodule\n";

  auto r = ParseWithPreprocessor(InSv2009(kSrc));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  bool cu_let_seen = false;
  for (auto* item : r.cu->cu_items) {
    if (item->kind == ModuleItemKind::kLetDecl && item->name == "gain") {
      EXPECT_NE(item->init_expr, nullptr);
      cu_let_seen = true;
    }
  }
  EXPECT_TRUE(cu_let_seen);

  auto& items = r.cu->modules[0]->items;
  auto* sum = FindItemByKind(items, ModuleItemKind::kLetDecl);
  ASSERT_NE(sum, nullptr);
  EXPECT_EQ(sum->name, "sum");
  ASSERT_EQ(sum->func_args.size(), 2u);
  EXPECT_EQ(sum->func_args[0].name, "x");
  EXPECT_EQ(sum->func_args[0].data_type.kind, DataTypeKind::kImplicit);
  EXPECT_EQ(sum->func_args[1].name, "y");
  EXPECT_EQ(sum->func_args[1].data_type.kind, DataTypeKind::kInt);

  EXPECT_NE(FindItemByKind(items, ModuleItemKind::kClockingBlock), nullptr);
  auto* init = FindItemByKind(items, ModuleItemKind::kInitialBlock);
  ASSERT_NE(init, nullptr);
  ASSERT_NE(init->body, nullptr);
  bool block_let_seen = false;
  for (auto* s : init->body->stmts) {
    if (s != nullptr && s->kind == StmtKind::kBlockItemDecl &&
        s->decl_item != nullptr &&
        s->decl_item->kind == ModuleItemKind::kLetDecl) {
      EXPECT_EQ(s->decl_item->name, "inner");
      block_let_seen = true;
    }
  }
  EXPECT_TRUE(block_let_seen);

  auto before = ParseWithPreprocessor(InSv2005(kSrc));
  EXPECT_TRUE(ReportedError(before.diags, "expected top-level declaration",
                            LineInRegion(1), "3.12.1"));
}

TEST(CompilerDirectiveParsing,
     SystemVerilog2009AddedQualifierWordsOpenConstructs) {
  const std::string kSrc =
      "module m (input logic clk, input logic req);\n"
      "  logic [1:0] sel;\n"
      "  logic [7:0] r;\n"
      "  global clocking gcb @(posedge clk); endclocking\n"
      "  restrict property (@(posedge clk) req);\n"
      "  initial begin\n"
      "    unique0 case (sel) 2'b01: r = 8'd1; default: r = 8'd0; endcase\n"
      "    unique0 casez (sel) 2'b1?: r = 8'd2; default: r = 8'd0; endcase\n"
      "    unique0 if (req) r = 8'd3; else r = 8'd4;\n"
      "  end\n"
      "endmodule\n";

  auto r = ParseWithPreprocessor(InSv2009(kSrc));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto& items = r.cu->modules[0]->items;
  EXPECT_NE(FindItemByKind(items, ModuleItemKind::kRestrictProperty), nullptr);

  auto* clocking = FindItemByKind(items, ModuleItemKind::kClockingBlock);
  ASSERT_NE(clocking, nullptr);
  EXPECT_TRUE(clocking->is_global_clocking);
  EXPECT_FALSE(clocking->is_default_clocking);

  auto* init = FindItemByKind(items, ModuleItemKind::kInitialBlock);
  ASSERT_NE(init, nullptr);
  ASSERT_NE(init->body, nullptr);
  size_t qualified = 0;
  for (auto* s : init->body->stmts) {
    if (s == nullptr) continue;
    if (s->kind == StmtKind::kCase || s->kind == StmtKind::kIf) {
      EXPECT_EQ(s->qualifier, CaseQualifier::kUnique0);
      ++qualified;
    }
  }
  EXPECT_EQ(qualified, 3u);

  auto before = ParseWithPreprocessor(InSv2005(kSrc));
  EXPECT_TRUE(ReportedError(before.diags, "expected ';', got 'clocking'",
                            LineInRegion(4), "6.8"));
}

TEST(CompilerDirectiveParsing,
     SystemVerilog2009AddedTemporalWordsBuildPropertyExpressions) {
  struct Operator {
    const char* word;
    const char* body;
  };
  const Operator kOperators[] = {
      {"eventually", "eventually [0:2] a"},
      {"s_eventually", "s_eventually a"},
      {"nexttime", "nexttime a"},
      {"s_nexttime", "s_nexttime a"},
      {"s_always", "s_always [0:1] a"},
      {"until", "a until b"},
      {"s_until", "a s_until b"},
      {"until_with", "a until_with b"},
      {"s_until_with", "a s_until_with b"},
      {"implies", "a implies b"},
      {"accept_on", "accept_on(b) a"},
      {"reject_on", "reject_on(b) a"},
      {"sync_accept_on", "sync_accept_on(b) a"},
      {"sync_reject_on", "sync_reject_on(b) a"},
      {"strong", "strong(##1 a)"},
      {"weak", "weak(##1 a)"},
  };
  EXPECT_EQ(std::size(kOperators), 16u);

  for (const auto& op : kOperators) {
    std::string src =
        std::string(
            "module m (input logic clk, input logic a, input logic b);\n"
            "  property p;\n"
            "    @(posedge clk) ") +
        op.body +
        ";\n"
        "  endproperty\n"
        "  assert property (p);\n"
        "endmodule\n";

    auto r = ParseWithPreprocessor(InSv2009(src));
    ASSERT_NE(r.cu, nullptr) << op.word;
    EXPECT_FALSE(r.has_errors) << op.word;
    EXPECT_TRUE(HasItemKindNamed(r.cu->modules[0]->items,
                                 ModuleItemKind::kPropertyDecl, "p"))
        << op.word;
  }
}

TEST(CompilerDirectiveParsing,
     SystemVerilog2009AddedTemporalWordsCarryTheirOwnOperandRules) {
  auto property_src = [](const char* body) {
    return std::string(
               "module m (input logic clk, input logic a);\n"
               "  property p;\n"
               "    @(posedge clk) ") +
           body +
           ";\n"
           "  endproperty\n"
           "  assert property (p);\n"
           "endmodule\n";
  };

  struct Form {
    const char* word;
    const char* bad;
    const char* good;
    const char* message;
    const char* subclause;
  };
  const Form kForms[] = {
      {"nexttime", "nexttime [-1] ##1 a", "nexttime [1] a",
       "nexttime index must be a non-negative integer constant expression",
       "16.12.10"},
      {"s_nexttime", "s_nexttime [-1] ##1 a", "s_nexttime [1] a",
       "nexttime index must be a non-negative integer constant expression",
       "16.12.10"},
      {"s_always", "s_always [1:$] ##1 a", "s_always [1:2] a",
       "s_always needs a finite range", "16.12.11"},
      {"eventually", "eventually [1:$] ##1 a", "eventually [1:2] a",
       "weak eventually needs a finite range", "16.12.13"},
      {"s_eventually", "s_eventually [3:1] ##1 a", "s_eventually [1:$] a",
       "eventually range minimum must not exceed the maximum", "16.12.13"},
  };

  for (const auto& f : kForms) {
    auto rejected = ParseWithPreprocessor(InSv2009(property_src(f.bad)));
    EXPECT_TRUE(
        ReportedError(rejected.diags, f.message, LineInRegion(3), f.subclause))
        << f.word << " is read as an operator here, so its operand is checked";
    EXPECT_TRUE(ParseWithPreprocessorOk(InSv2009(property_src(f.good))))
        << f.word << " takes the well-formed operand";
    EXPECT_TRUE(ParseWithPreprocessorOk(InSv2005(property_src(f.bad))))
        << f.word << " is an ordinary identifier under the included lists";
  }
}

TEST(CompilerDirectiveParsing,
     SystemVerilog2009IncludedVerilog1995WordsStillWork) {
  ExpectVerilog1995ConstructsParse("1800-2009");
}

TEST(CompilerDirectiveParsing, SystemVerilog2009IncludesTheConfigurationWords) {
  ExpectConfigurationWordsParse("1800-2009");
}

TEST(CompilerDirectiveParsing,
     SystemVerilog2009IncludedVerilog2001WordsStillWork) {
  ExpectVerilog2001ConstructsParse("1800-2009");
}

TEST(CompilerDirectiveParsing,
     SystemVerilog2009IncludedSystemVerilog2005WordsStillWork) {
  ExpectSystemVerilog2005ConstructsParse("1800-2009");
}

TEST(CompilerDirectiveParsing, SystemVerilog2009LeavesLaterWordsAsIdentifiers) {
  const char* const kLater[] = {"implements", "interconnect", "nettype",
                                "soft"};
  for (const char* word : kLater) {
    auto r = ParseWithPreprocessor(InSv2009(VarDecl(word)));
    ASSERT_NE(r.cu, nullptr) << word;
    EXPECT_FALSE(r.has_errors) << word;
    ASSERT_EQ(r.cu->modules.size(), 1u) << word;
    EXPECT_TRUE(HasItemKindNamed(r.cu->modules[0]->items,
                                 ModuleItemKind::kVarDecl, word))
        << word;

    std::string as_type =
        std::string("module m;\n  ") + word + " [7:0] v;\nendmodule\n";
    auto typed = ParseWithPreprocessor(InSv2009(as_type));
    EXPECT_TRUE(ReportedError(typed.diags, "expected ';', got '['",
                              LineInRegion(2), "6.8"))
        << word << " is not a data type under this version";

    auto later = ParseWithPreprocessor(InSv2012(VarDecl(word)));
    EXPECT_TRUE(ReportedError(
        later.diags, std::string("expected identifier, got '") + word + "'",
        LineInRegion(2), "6.8"))
        << word << " is reserved by the version after this one";
  }
}

}  // namespace
