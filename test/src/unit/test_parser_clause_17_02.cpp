// §17.2: Checker declaration

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

// =============================================================================
// Parse-level fixture
// =============================================================================
struct CheckerParseTest : ::testing::Test {
 protected:
  CompilationUnit *Parse(const std::string &src) {
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

static bool HasItemOfKind(const std::vector<ModuleItem *> &items,
                          ModuleItemKind kind) {
  for (const auto *item : items) {
    if (item->kind == kind) return true;
  }
  return false;
}

namespace {

// =============================================================================
// §17.1 Basic checker declaration
// =============================================================================
TEST_F(CheckerParseTest, EmptyChecker) {
  auto *unit = Parse("checker my_check; endchecker");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_EQ(unit->checkers[0]->name, "my_check");
  EXPECT_EQ(unit->checkers[0]->decl_kind, ModuleDeclKind::kChecker);
  EXPECT_TRUE(unit->checkers[0]->ports.empty());
  EXPECT_TRUE(unit->checkers[0]->items.empty());
}

TEST_F(CheckerParseTest, CheckerWithEndLabel) {
  auto *unit = Parse(R"(
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
  auto *unit = Parse(R"(
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
  auto *unit = Parse(R"(
    checker out_check(input logic clk, output logic valid);
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  ASSERT_GE(unit->checkers[0]->ports.size(), 2u);
  EXPECT_EQ(unit->checkers[0]->ports[1].name, "valid");
  EXPECT_EQ(unit->checkers[0]->ports[1].direction, Direction::kOutput);
}

TEST_F(CheckerParseTest, CheckerWithNoPorts) {
  auto *unit = Parse(R"(
    checker no_ports;
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_TRUE(unit->checkers[0]->ports.empty());
}

TEST_F(CheckerParseTest, CheckerWithEmptyParenPorts) {
  auto *unit = Parse(R"(
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
  auto *unit = Parse(R"(
    checker prop_check(input logic clk, input logic a, input logic b);
      property p1;
        a |-> b;
      endproperty
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_FALSE(unit->checkers[0]->items.empty());
  EXPECT_TRUE(
      HasItemOfKind(unit->checkers[0]->items, ModuleItemKind::kPropertyDecl));
}

TEST_F(CheckerParseTest, CheckerWithSequenceDecl) {
  auto *unit = Parse(R"(
    checker seq_check(input logic clk, input logic a);
      sequence s1;
        a;
      endsequence
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_FALSE(unit->checkers[0]->items.empty());
  EXPECT_TRUE(
      HasItemOfKind(unit->checkers[0]->items, ModuleItemKind::kSequenceDecl));
}

// =============================================================================
// §17.7 Multiple checkers
// =============================================================================
TEST_F(CheckerParseTest, MultipleCheckers) {
  auto *unit = Parse(R"(
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
  auto *unit = Parse(R"(
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
  auto *unit = Parse(R"(
    checker assert_check(input logic clk, input logic a, input logic b);
      assert property (@(posedge clk) a |-> b);
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(unit->checkers[0]->items, ModuleItemKind::kAssertProperty));
}

// =============================================================================
// §17.13 Checker with continuous assignment
// =============================================================================
TEST_F(CheckerParseTest, CheckerWithContAssign) {
  auto *unit = Parse(R"(
    checker assign_check;
      logic a, b;
      assign a = b;
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(unit->checkers[0]->items, ModuleItemKind::kContAssign));
}

// --- Test helpers ---
struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// Returns true if any item in the list matches the given kind.
bool HasItemKind(const std::vector<ModuleItem *> &items, ModuleItemKind kind) {
  for (auto *item : items) {
    if (item->kind == kind) return true;
  }
  return false;
}

// =============================================================================
// A.1.8 Checker items
// =============================================================================
// checker_port_list / checker_port_item / checker_port_direction
TEST(SourceText, CheckerPortList) {
  auto r = Parse(
      "checker chk(input logic clk, output bit valid);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  auto *chk = r.cu->checkers[0];
  EXPECT_EQ(chk->name, "chk");
  EXPECT_EQ(chk->decl_kind, ModuleDeclKind::kChecker);
  ASSERT_EQ(chk->ports.size(), 2u);
  EXPECT_EQ(chk->ports[0].direction, Direction::kInput);
  EXPECT_EQ(chk->ports[0].name, "clk");
  EXPECT_EQ(chk->ports[1].direction, Direction::kOutput);
  EXPECT_EQ(chk->ports[1].name, "valid");
}

// checker_port_item with default value (= property_actual_arg)
TEST(SourceText, CheckerPortDefaultValue) {
  auto r = Parse(
      "checker chk(input logic clk = 1'b0);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_EQ(r.cu->checkers[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->ports[0].direction, Direction::kInput);
  EXPECT_EQ(r.cu->checkers[0]->ports[0].name, "clk");
  EXPECT_NE(r.cu->checkers[0]->ports[0].default_value, nullptr);
}

// checker_or_generate_item ::= continuous_assign
TEST(SourceText, CheckerContinuousAssign) {
  auto r = Parse(
      "checker chk;\n"
      "  assign a = b;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_GE(r.cu->checkers[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->items[0]->kind, ModuleItemKind::kContAssign);
}

// checker_or_generate_item ::= initial_construct | always_construct |
// final_construct
TEST(SourceText, CheckerInitialAlwaysFinal) {
  auto r = Parse(
      "checker chk;\n"
      "  initial begin end\n"
      "  always @(posedge clk) x <= 1;\n"
      "  final begin end\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  auto &items = r.cu->checkers[0]->items;
  ASSERT_GE(items.size(), 3u);
  EXPECT_TRUE(HasItemKind(items, ModuleItemKind::kInitialBlock));
  EXPECT_TRUE(HasItemKind(items, ModuleItemKind::kAlwaysBlock));
  EXPECT_TRUE(HasItemKind(items, ModuleItemKind::kFinalBlock));
}

// checker_or_generate_item ::= assertion_item
TEST(SourceText, CheckerAssertionItem) {
  auto r = Parse(
      "checker chk;\n"
      "  assert property (@(posedge clk) a |-> b);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_GE(r.cu->checkers[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->items[0]->kind, ModuleItemKind::kAssertProperty);
}

// checker_or_generate_item_declaration ::= checker_declaration (nested)
TEST(SourceText, CheckerNestedChecker) {
  auto r = Parse(
      "checker outer;\n"
      "  checker inner;\n"
      "    logic a;\n"
      "  endchecker\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->name, "outer");
}

// checker_or_generate_item_declaration ::= genvar_declaration
TEST(SourceText, CheckerGenvarDecl) {
  auto r = Parse(
      "checker chk;\n"
      "  genvar i;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_GE(r.cu->checkers[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(r.cu->checkers[0]->items[0]->name, "i");
}

// checker_or_generate_item_declaration ::= default disable iff expr ;
TEST(SourceText, CheckerDefaultDisableIff) {
  auto r = Parse(
      "checker chk;\n"
      "  default disable iff rst;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_GE(r.cu->checkers[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->items[0]->kind,
            ModuleItemKind::kDefaultDisableIff);
}

// checker_generate_item ::= loop | conditional | generate_region | elab task
TEST(SourceText, CheckerGenerateItems) {
  auto r = Parse(
      "checker chk;\n"
      "  for (genvar i = 0; i < 4; i++) begin end\n"
      "  if (1) begin end\n"
      "  generate endgenerate\n"
      "  $info(\"checker ok\");\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  auto &items = r.cu->checkers[0]->items;
  EXPECT_TRUE(HasItemKind(items, ModuleItemKind::kGenerateFor));
  EXPECT_TRUE(HasItemKind(items, ModuleItemKind::kGenerateIf));
  EXPECT_TRUE(HasItemKind(items, ModuleItemKind::kElabSystemTask));
}

// Combined: checker with multiple A.1.8 item types.
TEST(SourceText, CheckerMultipleItemTypes) {
  auto r = Parse(
      "checker chk(input logic clk, output bit ok);\n"
      "  logic sig;\n"
      "  assign ok = sig;\n"
      "  initial begin end\n"
      "  always @(posedge clk) sig <= 1;\n"
      "  final begin end\n"
      "  assert property (@(posedge clk) sig);\n"
      "  default disable iff !ok;\n"
      "  function int f(); return 0; endfunction\n"
      "  $warning(\"test\");\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  auto *chk = r.cu->checkers[0];
  EXPECT_EQ(chk->name, "chk");
  ASSERT_EQ(chk->ports.size(), 2u);
  EXPECT_TRUE(HasItemKind(chk->items, ModuleItemKind::kVarDecl));
  EXPECT_TRUE(HasItemKind(chk->items, ModuleItemKind::kContAssign));
  EXPECT_TRUE(HasItemKind(chk->items, ModuleItemKind::kInitialBlock));
  EXPECT_TRUE(HasItemKind(chk->items, ModuleItemKind::kAlwaysBlock));
  EXPECT_TRUE(HasItemKind(chk->items, ModuleItemKind::kFinalBlock));
  EXPECT_TRUE(HasItemKind(chk->items, ModuleItemKind::kAssertProperty));
  EXPECT_TRUE(HasItemKind(chk->items, ModuleItemKind::kDefaultDisableIff));
  EXPECT_TRUE(HasItemKind(chk->items, ModuleItemKind::kFunctionDecl));
  EXPECT_TRUE(HasItemKind(chk->items, ModuleItemKind::kElabSystemTask));
}

// description: checker_declaration
TEST(SourceText, DescriptionChecker) {
  auto r = Parse("checker chk; endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->name, "chk");
}

// =============================================================================
// A.1.2 checker_declaration
// =============================================================================
// Checker with ports.
TEST(SourceText, CheckerWithPorts) {
  auto r = Parse("checker chk(event clk); endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->name, "chk");
}

}  // namespace
