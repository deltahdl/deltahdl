// §9.2.2.2: Combinational logic always_comb procedure

#include "fixture_parser.h"
#include "simulator/udp_eval.h"

using namespace delta;

static std::vector<ModuleItem*> FindUdpInsts(
    const std::vector<ModuleItem*>& items) {
  std::vector<ModuleItem*> insts;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kUdpInst) insts.push_back(item);
  }
  return insts;
}

static std::vector<ModuleItem*> FindContAssigns(
    const std::vector<ModuleItem*>& items) {
  std::vector<ModuleItem*> result;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kContAssign) result.push_back(item);
  }
  return result;
}

// Helpers to extract items from the first module.
static ModuleItem* FindItem(const std::vector<ModuleItem*>& items,
                            ModuleItemKind kind) {
  for (auto* item : items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

static std::vector<ModuleItem*> FindItems(const std::vector<ModuleItem*>& items,
                                          ModuleItemKind kind) {
  std::vector<ModuleItem*> result;
  for (auto* item : items) {
    if (item->kind == kind) result.push_back(item);
  }
  return result;
}

namespace {

TEST(ParserA602, AlwaysConstruct_AlwaysComb) {
  auto r = Parse(
      "module m;\n"
      "  always_comb y = a & b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kAlwaysBlock);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysComb);
}

struct ParseResult9h {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9h Parse(const std::string& src) {
  ParseResult9h result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// ---------------------------------------------------------------------------
// 7. always_comb with nested if-else and case
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_NestedIfElseAndCase) {
  auto r = Parse(
      "module m;\n"
      "  logic mode;\n"
      "  logic [1:0] sel;\n"
      "  logic [7:0] out;\n"
      "  always_comb begin\n"
      "    if (mode) begin\n"
      "      case (sel)\n"
      "        2'd0: out = 8'd10;\n"
      "        2'd1: out = 8'd20;\n"
      "        default: out = 8'd0;\n"
      "      endcase\n"
      "    end else begin\n"
      "      out = 8'd0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstAlwaysCombStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_NE(stmt->then_branch, nullptr);
  EXPECT_NE(stmt->else_branch, nullptr);
  // The then branch should be a block containing a case statement
  ASSERT_EQ(stmt->then_branch->kind, StmtKind::kBlock);
  ASSERT_GE(stmt->then_branch->stmts.size(), 1u);
  EXPECT_EQ(stmt->then_branch->stmts[0]->kind, StmtKind::kCase);
}

// ---------------------------------------------------------------------------
// 8. always_comb with for loop
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_ForLoop) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] data_in [0:3];\n"
      "  logic [7:0] data_out [0:3];\n"
      "  always_comb begin\n"
      "    for (int i = 0; i < 4; i++)\n"
      "      data_out[i] = data_in[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstAlwaysCombStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_NE(stmt->for_cond, nullptr);
  EXPECT_NE(stmt->for_body, nullptr);
}

struct ParseResult9e {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9e Parse(const std::string& src) {
  ParseResult9e result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =============================================================================
// LRM section 9.3.1 -- Blocks in various procedural contexts.
// =============================================================================
TEST(ParserSection9, Sec9_3_1_BlockInAlwaysComb) {
  auto r = Parse(
      "module m;\n"
      "  always_comb begin\n"
      "    x = a & b;\n"
      "    y = a | c;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysCombBlock);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_EQ(item->body->stmts.size(), 2u);
}

// Helper for block 12: verify always block has 3 blocking assigns.
static void VerifyAlwaysMultiAssigns(ParseResult& r) {
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_EQ(item->body->stmts.size(), 3u);
  for (size_t i = 0; i < 3; ++i) {
    EXPECT_EQ(item->body->stmts[i]->kind, StmtKind::kBlockingAssign);
  }
}

struct ParseResult9i {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9i Parse(const std::string& src) {
  ParseResult9i result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// ---------------------------------------------------------------------------
// 23. always_comb with multiple assignment statements.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysCombMultipleAssigns) {
  auto r = Parse(
      "module m;\n"
      "  always_comb begin\n"
      "    x = a & b;\n"
      "    y = a | c;\n"
      "    z = a ^ d;\n"
      "  end\n"
      "endmodule\n");
  VerifyAlwaysMultiAssigns(r);
}

// ---------------------------------------------------------------------------
// 15. always_comb with multiple variable assignments
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_MultipleAssignments) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, c, x, y, z;\n"
      "  always_comb begin\n"
      "    x = a & b;\n"
      "    y = a | c;\n"
      "    z = b ^ c;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_EQ(item->body->stmts.size(), 3u);
  for (size_t i = 0; i < 3; ++i) {
    EXPECT_EQ(item->body->stmts[i]->kind, StmtKind::kBlockingAssign);
  }
}

// Helper for block 24: verify always block has nested if-else.
static void VerifyAlwaysNestedIfElse(ParseResult& r) {
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 1u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kIf);
}

// ---------------------------------------------------------------------------
// 27. always_comb with nested if-else inside begin-end.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysCombNestedIfElseInBlock) {
  auto r = Parse(
      "module m;\n"
      "  always_comb begin\n"
      "    if (a)\n"
      "      if (b) y = 1;\n"
      "      else y = 2;\n"
      "    else\n"
      "      y = 0;\n"
      "  end\n"
      "endmodule\n");
  VerifyAlwaysNestedIfElse(r);
}

struct ParseResult4d {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult4d Parse(const std::string& src) {
  ParseResult4d result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =============================================================================
// §4.6: always_comb with case inside
// =============================================================================
TEST(ParserSection4, Sec4_6_AlwaysCombWithCaseInside) {
  auto r = Parse(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [3:0] y;\n"
      "  always_comb begin\n"
      "    case (sel)\n"
      "      2'b00: y = 4'h0;\n"
      "      2'b01: y = 4'h1;\n"
      "      2'b10: y = 4'h2;\n"
      "      default: y = 4'hf;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysComb);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 1u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kCase);
}

// ---------------------------------------------------------------------------
// 24. Multiple always_comb blocks in the same module
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_MultipleAlwaysCombBlocks) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, x, y;\n"
      "  always_comb x = a & b;\n"
      "  always_comb y = a | b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* first = NthAlwaysComb(r, 0);
  auto* second = NthAlwaysComb(r, 1);
  ASSERT_NE(first, nullptr);
  ASSERT_NE(second, nullptr);
  EXPECT_EQ(first->kind, ModuleItemKind::kAlwaysCombBlock);
  EXPECT_EQ(second->kind, ModuleItemKind::kAlwaysCombBlock);
  ASSERT_NE(first->body, nullptr);
  ASSERT_NE(second->body, nullptr);
}

// ---------------------------------------------------------------------------
// 25. always_comb with array indexing
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_ArrayIndexing) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] mem [0:15];\n"
      "  logic [3:0] addr;\n"
      "  logic [7:0] data;\n"
      "  always_comb data = mem[addr];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->rhs, nullptr);
  EXPECT_EQ(item->body->rhs->kind, ExprKind::kSelect);
}

struct ParseResult6j {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult6j Parse(const std::string& src) {
  ParseResult6j result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// 14. Variable driven by always_comb.
TEST(ParserSection6, Sec6_5_VarDrivenByAlwaysComb) {
  auto r = Parse(
      "module t;\n"
      "  logic a, y;\n"
      "  always_comb y = a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  bool found_comb = false;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kAlwaysCombBlock) {
      found_comb = true;
      ASSERT_NE(item->body, nullptr);
    }
  }
  EXPECT_TRUE(found_comb);
}

// =============================================================================
// §4.6: always_comb with multiple outputs
// =============================================================================
TEST(ParserSection4, Sec4_6_AlwaysCombMultipleOutputs) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, sum, carry;\n"
      "  always_comb begin\n"
      "    sum = a ^ b;\n"
      "    carry = a & b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysComb);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_GE(item->body->stmts.size(), 2u);
}

// ---------------------------------------------------------------------------
// 30. always_comb ParseOk smoke test for full mux with for loop and array
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_ParseOkComplexMuxPattern) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic [3:0] sel;\n"
              "  logic [7:0] inputs [0:15];\n"
              "  logic [7:0] out;\n"
              "  always_comb begin\n"
              "    out = 8'd0;\n"
              "    for (int i = 0; i < 16; i++) begin\n"
              "      if (sel == i[3:0])\n"
              "        out = inputs[i];\n"
              "    end\n"
              "  end\n"
              "endmodule\n"));
}

// Return the first always-kind module item (any always variant).
static ModuleItem* FirstAlwaysItem(ParseResult9h& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock) return item;
  }
  return nullptr;
}

// =============================================================================
// LRM section 9.2.2.2 -- always_comb compared with always @*
//
// Both always_comb and always @* describe combinational logic. The parser
// produces AlwaysKind::kAlwaysComb for always_comb and AlwaysKind::kAlways
// for always @*. For always @*, the parser consumes the @* at the
// module-item level (not as a statement-level event control), so both
// forms have the body directly on item->body with empty sensitivity.
// =============================================================================
// ---------------------------------------------------------------------------
// 1. always_comb parses with AlwaysKind::kAlwaysComb.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysCombAlwaysKind) {
  auto r = Parse(
      "module m;\n"
      "  always_comb a = b & c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysComb);
}

struct ParseResult4c {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult4c Parse(const std::string& src) {
  ParseResult4c result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// Returns the first always_* item from the first module.
static ModuleItem* FirstAlwaysItem(ParseResult4c& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysCombBlock ||
        item->kind == ModuleItemKind::kAlwaysFFBlock ||
        item->kind == ModuleItemKind::kAlwaysLatchBlock ||
        item->kind == ModuleItemKind::kAlwaysBlock)
      return item;
  }
  return nullptr;
}

// ---------------------------------------------------------------------------
// 19. always_comb block (scheduling semantics)
// ---------------------------------------------------------------------------
TEST(ParserSection4, Sec4_5_AlwaysComb) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b, c;\n"
      "  always_comb a = b & c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysBlock);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysComb);
  ASSERT_NE(item->body, nullptr);
}

// ---------------------------------------------------------------------------
// 6. always_comb body is directly on item->body (single assignment).
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysCombBodyDirectAssign) {
  auto r = Parse(
      "module m;\n"
      "  always_comb x = a ^ b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
}

// ---------------------------------------------------------------------------
// 8. always_comb with begin-end block body.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysCombBeginEndBlock) {
  auto r = Parse(
      "module m;\n"
      "  always_comb begin\n"
      "    x = a & b;\n"
      "    y = a | c;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysComb);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_EQ(item->body->stmts.size(), 2u);
}

}  // namespace
