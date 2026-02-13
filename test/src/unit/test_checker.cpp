// Tests for §17 Checker declarations — parsing and elaboration/simulation.

#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"

using namespace delta;

namespace {

// =============================================================================
// Parse-level fixture
// =============================================================================

struct CheckerParseTest : ::testing::Test {
 protected:
  CompilationUnit* Parse(const std::string& src) {
    source_ = src;
    lexer_ = std::make_unique<Lexer>(source_, 0, diag_);
    parser_ = std::make_unique<Parser>(*lexer_, arena_, diag_);
    return parser_->Parse();
  }

  SourceManager mgr_;
  Arena arena_;
  DiagEngine diag_{mgr_};
  std::string source_;
  std::unique_ptr<Lexer> lexer_;
  std::unique_ptr<Parser> parser_;
};

// =============================================================================
// Elaboration fixture
// =============================================================================

struct CheckerElabFixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
};

static RtlirDesign* ElaborateSource(const std::string& src,
                                    CheckerElabFixture& f,
                                    std::string_view top_name) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(top_name);
}

// =============================================================================
// §17.1 Basic checker declaration
// =============================================================================

TEST_F(CheckerParseTest, EmptyChecker) {
  auto* unit = Parse("checker my_check; endchecker");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_EQ(unit->checkers[0]->name, "my_check");
  EXPECT_EQ(unit->checkers[0]->decl_kind, ModuleDeclKind::kChecker);
  EXPECT_TRUE(unit->checkers[0]->ports.empty());
  EXPECT_TRUE(unit->checkers[0]->items.empty());
}

TEST_F(CheckerParseTest, CheckerWithEndLabel) {
  auto* unit = Parse(R"(
    checker labeled_check;
    endchecker : labeled_check
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_EQ(unit->checkers[0]->name, "labeled_check");
}

// =============================================================================
// §17.2 Checker ports
// =============================================================================

TEST_F(CheckerParseTest, CheckerWithInputPorts) {
  auto* unit = Parse(R"(
    checker port_check(input logic clk, input logic rst);
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  ASSERT_GE(unit->checkers[0]->ports.size(), 2u);
  EXPECT_EQ(unit->checkers[0]->ports[0].name, "clk");
  EXPECT_EQ(unit->checkers[0]->ports[0].direction, Direction::kInput);
  EXPECT_EQ(unit->checkers[0]->ports[1].name, "rst");
  EXPECT_EQ(unit->checkers[0]->ports[1].direction, Direction::kInput);
}

TEST_F(CheckerParseTest, CheckerWithOutputPorts) {
  auto* unit = Parse(R"(
    checker out_check(input logic clk, output logic valid);
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  ASSERT_GE(unit->checkers[0]->ports.size(), 2u);
  EXPECT_EQ(unit->checkers[0]->ports[1].name, "valid");
  EXPECT_EQ(unit->checkers[0]->ports[1].direction, Direction::kOutput);
}

TEST_F(CheckerParseTest, CheckerWithNoPorts) {
  auto* unit = Parse(R"(
    checker no_ports;
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_TRUE(unit->checkers[0]->ports.empty());
}

TEST_F(CheckerParseTest, CheckerWithEmptyParenPorts) {
  auto* unit = Parse(R"(
    checker empty_parens();
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_TRUE(unit->checkers[0]->ports.empty());
}

// =============================================================================
// §17.3 Checker body with properties and sequences
// =============================================================================

TEST_F(CheckerParseTest, CheckerWithPropertyDecl) {
  auto* unit = Parse(R"(
    checker prop_check(input logic clk, input logic a, input logic b);
      property p1;
        a |-> b;
      endproperty
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_FALSE(unit->checkers[0]->items.empty());
  bool found_property = false;
  for (const auto* item : unit->checkers[0]->items) {
    if (item->kind == ModuleItemKind::kPropertyDecl) found_property = true;
  }
  EXPECT_TRUE(found_property);
}

TEST_F(CheckerParseTest, CheckerWithSequenceDecl) {
  auto* unit = Parse(R"(
    checker seq_check(input logic clk, input logic a);
      sequence s1;
        a;
      endsequence
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_FALSE(unit->checkers[0]->items.empty());
  bool found_seq = false;
  for (const auto* item : unit->checkers[0]->items) {
    if (item->kind == ModuleItemKind::kSequenceDecl) found_seq = true;
  }
  EXPECT_TRUE(found_seq);
}

// =============================================================================
// §17.4 Checker variables
// =============================================================================

TEST_F(CheckerParseTest, CheckerWithVariables) {
  auto* unit = Parse(R"(
    checker var_check;
      logic a, b;
      assign a = b;
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_FALSE(unit->checkers[0]->items.empty());
}

TEST_F(CheckerParseTest, CheckerWithBitVector) {
  auto* unit = Parse(R"(
    checker bv_check;
      logic [7:0] counter;
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_FALSE(unit->checkers[0]->items.empty());
}

// =============================================================================
// §17.5 Checker procedures (always, initial)
// =============================================================================

TEST_F(CheckerParseTest, CheckerWithAlwaysBlock) {
  auto* unit = Parse(R"(
    checker always_check(input logic clk, input logic a);
      always @(posedge clk)
        assert(a);
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  bool found_always = false;
  for (const auto* item : unit->checkers[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock) found_always = true;
  }
  EXPECT_TRUE(found_always);
}

TEST_F(CheckerParseTest, CheckerWithInitialBlock) {
  auto* unit = Parse(R"(
    checker init_check;
      initial begin
        $display("checker started");
      end
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  bool found_initial = false;
  for (const auto* item : unit->checkers[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) found_initial = true;
  }
  EXPECT_TRUE(found_initial);
}

// =============================================================================
// §17.6 Checker instantiation
// =============================================================================

TEST_F(CheckerParseTest, CheckerInstantiatedInModule) {
  auto* unit = Parse(R"(
    checker my_checker(input logic clk, input logic data);
    endchecker

    module top;
      logic clk, data;
      my_checker chk_inst(.clk(clk), .data(data));
    endmodule
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  ASSERT_EQ(unit->modules.size(), 1u);
  bool found_inst = false;
  for (const auto* item : unit->modules[0]->items) {
    if (item->kind == ModuleItemKind::kModuleInst) {
      found_inst = true;
      EXPECT_EQ(item->inst_module, "my_checker");
      EXPECT_EQ(item->inst_name, "chk_inst");
    }
  }
  EXPECT_TRUE(found_inst);
}

// =============================================================================
// §17.7 Multiple checkers
// =============================================================================

TEST_F(CheckerParseTest, MultipleCheckers) {
  auto* unit = Parse(R"(
    checker c1; endchecker
    checker c2; endchecker
    checker c3; endchecker
  )");
  EXPECT_EQ(unit->checkers.size(), 3u);
  EXPECT_EQ(unit->checkers[0]->name, "c1");
  EXPECT_EQ(unit->checkers[1]->name, "c2");
  EXPECT_EQ(unit->checkers[2]->name, "c3");
}

// =============================================================================
// §17.8 Checker coexists with module and program
// =============================================================================

TEST_F(CheckerParseTest, CheckerCoexistsWithModuleAndProgram) {
  auto* unit = Parse(R"(
    module m; endmodule
    program p; endprogram
    checker c; endchecker
  )");
  EXPECT_EQ(unit->modules.size(), 1u);
  EXPECT_EQ(unit->programs.size(), 1u);
  EXPECT_EQ(unit->checkers.size(), 1u);
}

// =============================================================================
// §17.9 Checker with assert property
// =============================================================================

TEST_F(CheckerParseTest, CheckerWithAssertProperty) {
  auto* unit = Parse(R"(
    checker assert_check(input logic clk, input logic a, input logic b);
      assert property (@(posedge clk) a |-> b);
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  bool found_assert = false;
  for (const auto* item : unit->checkers[0]->items) {
    if (item->kind == ModuleItemKind::kAssertProperty) found_assert = true;
  }
  EXPECT_TRUE(found_assert);
}

// =============================================================================
// §17.10 Checker with function/task declarations
// =============================================================================

TEST_F(CheckerParseTest, CheckerWithFunctionDecl) {
  auto* unit = Parse(R"(
    checker func_check;
      function int get_val;
        return 42;
      endfunction
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  bool found_func = false;
  for (const auto* item : unit->checkers[0]->items) {
    if (item->kind == ModuleItemKind::kFunctionDecl) found_func = true;
  }
  EXPECT_TRUE(found_func);
}

// =============================================================================
// §17.11 Checker elaboration — checker as elaboration target
// =============================================================================

TEST(CheckerElab, ElaborateCheckerWithVars) {
  CheckerElabFixture f;
  auto* design = ElaborateSource(
      "checker my_chk;\n"
      "  logic [7:0] count;\n"
      "  assign count = 8'hFF;\n"
      "endchecker\n",
      f, "my_chk");
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->name, "my_chk");
  EXPECT_FALSE(mod->variables.empty());
  EXPECT_FALSE(mod->assigns.empty());
}

TEST(CheckerElab, ElaborateCheckerWithPorts) {
  CheckerElabFixture f;
  auto* design = ElaborateSource(
      "checker chk_ports(input logic clk, input logic rst);\n"
      "endchecker\n",
      f, "chk_ports");
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->ports.size(), 2u);
  EXPECT_EQ(mod->ports[0].name, "clk");
  EXPECT_EQ(mod->ports[1].name, "rst");
}

// =============================================================================
// §17.12 Checker instantiation via elaboration
// =============================================================================

TEST(CheckerElab, CheckerInstantiatedFromModule) {
  CheckerElabFixture f;
  auto* design = ElaborateSource(
      "checker sub_chk(input logic a);\n"
      "endchecker\n"
      "module top;\n"
      "  logic sig;\n"
      "  sub_chk u0(.a(sig));\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1u);
  EXPECT_NE(mod->children[0].resolved, nullptr);
  EXPECT_EQ(mod->children[0].resolved->name, "sub_chk");
}

// =============================================================================
// §17.13 Checker with continuous assignment
// =============================================================================

TEST_F(CheckerParseTest, CheckerWithContAssign) {
  auto* unit = Parse(R"(
    checker assign_check;
      logic a, b;
      assign a = b;
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  bool found_assign = false;
  for (const auto* item : unit->checkers[0]->items) {
    if (item->kind == ModuleItemKind::kContAssign) found_assign = true;
  }
  EXPECT_TRUE(found_assign);
}

// =============================================================================
// §17.14 Checker with covergroup
// =============================================================================

TEST_F(CheckerParseTest, CheckerWithCovergroup) {
  auto* unit = Parse(R"(
    checker cov_check(input logic clk, input logic x);
      covergroup cg @(posedge clk);
        coverpoint x;
      endgroup
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  bool found_cg = false;
  for (const auto* item : unit->checkers[0]->items) {
    if (item->kind == ModuleItemKind::kCovergroupDecl) found_cg = true;
  }
  EXPECT_TRUE(found_cg);
}

}  // namespace
