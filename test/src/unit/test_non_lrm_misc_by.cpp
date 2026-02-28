// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

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

// Return the first always-kind module item (any always variant).
static ModuleItem* FirstAlwaysItem(ParseResult9h& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock) return item;
  }
  return nullptr;
}

// Return the Nth always-kind module item (0-indexed).
static ModuleItem* NthAlwaysItem(ParseResult9h& r, size_t n) {
  size_t count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock) {
      if (count == n) return item;
      ++count;
    }
  }
  return nullptr;
}

namespace {

// ---------------------------------------------------------------------------
// 13. always_comb with concatenation
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_Concatenation) {
  auto r = Parse(
      "module m;\n"
      "  logic [3:0] a, b;\n"
      "  logic [7:0] c;\n"
      "  always_comb c = {a, b};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->rhs, nullptr);
  EXPECT_EQ(item->body->rhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(item->body->rhs->elements.size(), 2u);
}

// ---------------------------------------------------------------------------
// 14. always_comb with replication
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_Replication) {
  auto r = Parse(
      "module m;\n"
      "  logic sign_bit;\n"
      "  logic [7:0] extended;\n"
      "  always_comb extended = {8{sign_bit}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->rhs, nullptr);
  EXPECT_EQ(item->body->rhs->kind, ExprKind::kReplicate);
  EXPECT_NE(item->body->rhs->repeat_count, nullptr);
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

// ---------------------------------------------------------------------------
// 16. always_comb with bit select on LHS
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_BitSelectLHS) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] data;\n"
      "  logic val;\n"
      "  always_comb data[3] = val;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->lhs, nullptr);
  EXPECT_EQ(item->body->lhs->kind, ExprKind::kSelect);
}

// ---------------------------------------------------------------------------
// 17. always_comb with part select on LHS
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_PartSelectLHS) {
  auto r = Parse(
      "module m;\n"
      "  logic [15:0] bus;\n"
      "  logic [7:0] low_byte;\n"
      "  always_comb bus[7:0] = low_byte;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->lhs, nullptr);
  EXPECT_EQ(item->body->lhs->kind, ExprKind::kSelect);
  EXPECT_NE(item->body->lhs->index, nullptr);
  EXPECT_NE(item->body->lhs->index_end, nullptr);
}

// ---------------------------------------------------------------------------
// 18. always_comb with struct member access
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_StructMemberAccess) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] addr;\n"
      "    logic [7:0] data;\n"
      "  } pkt_t;\n"
      "  pkt_t pkt;\n"
      "  logic [7:0] a, d;\n"
      "  always_comb begin\n"
      "    pkt.addr = a;\n"
      "    pkt.data = d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 2u);
  // LHS of first assignment should be a member access expression
  EXPECT_EQ(item->body->stmts[0]->lhs->kind, ExprKind::kMemberAccess);
  EXPECT_EQ(item->body->stmts[1]->lhs->kind, ExprKind::kMemberAccess);
}

// ---------------------------------------------------------------------------
// 19. always_comb with unique case
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_UniqueCase) {
  auto r = Parse(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [3:0] y;\n"
      "  always_comb begin\n"
      "    unique case (sel)\n"
      "      2'b00: y = 4'd0;\n"
      "      2'b01: y = 4'd1;\n"
      "      2'b10: y = 4'd2;\n"
      "      2'b11: y = 4'd3;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstAlwaysCombStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
  ASSERT_EQ(stmt->case_items.size(), 4u);
}

// ---------------------------------------------------------------------------
// 20. always_comb with priority case
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_PriorityCase) {
  auto r = Parse(
      "module m;\n"
      "  logic [3:0] req;\n"
      "  logic [1:0] grant;\n"
      "  always_comb begin\n"
      "    priority case (1'b1)\n"
      "      req[0]: grant = 2'd0;\n"
      "      req[1]: grant = 2'd1;\n"
      "      req[2]: grant = 2'd2;\n"
      "      req[3]: grant = 2'd3;\n"
      "      default: grant = 2'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstAlwaysCombStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
  ASSERT_EQ(stmt->case_items.size(), 5u);
}

// ---------------------------------------------------------------------------
// 21. always_comb with local variable declaration
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_LocalVarDecl) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] a, b, result;\n"
      "  always_comb begin\n"
      "    logic [8:0] temp;\n"
      "    temp = a + b;\n"
      "    result = temp[7:0];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 3u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(item->body->stmts[0]->var_name, "temp");
  EXPECT_EQ(item->body->stmts[1]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(item->body->stmts[2]->kind, StmtKind::kBlockingAssign);
}

// ---------------------------------------------------------------------------
// 22. always_comb has implicit sensitivity (no sensitivity list on item)
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_ImplicitSensitivity) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, c;\n"
      "  always_comb c = a ^ b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysCombBlock);
  // always_comb must not have an explicit sensitivity list
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
}

// ---------------------------------------------------------------------------
// 23. always_comb with complex combinational logic (priority encoder)
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_PriorityEncoderPattern) {
  auto r = Parse(
      "module m;\n"
      "  logic [3:0] req;\n"
      "  logic [1:0] enc;\n"
      "  logic valid;\n"
      "  always_comb begin\n"
      "    enc = 2'b00;\n"
      "    valid = 1'b0;\n"
      "    if (req[3]) begin\n"
      "      enc = 2'b11;\n"
      "      valid = 1'b1;\n"
      "    end else if (req[2]) begin\n"
      "      enc = 2'b10;\n"
      "      valid = 1'b1;\n"
      "    end else if (req[1]) begin\n"
      "      enc = 2'b01;\n"
      "      valid = 1'b1;\n"
      "    end else if (req[0]) begin\n"
      "      enc = 2'b00;\n"
      "      valid = 1'b1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  // Two default assignments plus an if-else-if chain
  ASSERT_GE(item->body->stmts.size(), 3u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(item->body->stmts[1]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(item->body->stmts[2]->kind, StmtKind::kIf);
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

// ---------------------------------------------------------------------------
// 26. always_comb with unique0 case
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_Unique0Case) {
  auto r = Parse(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [3:0] y;\n"
      "  always_comb begin\n"
      "    unique0 case (sel)\n"
      "      2'b00: y = 4'd0;\n"
      "      2'b01: y = 4'd1;\n"
      "      2'b10: y = 4'd2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstAlwaysCombStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique0);
  ASSERT_EQ(stmt->case_items.size(), 3u);
}

// ---------------------------------------------------------------------------
// 27. always_comb with concatenation on LHS
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_ConcatenationLHS) {
  auto r = Parse(
      "module m;\n"
      "  logic [3:0] hi, lo;\n"
      "  logic [7:0] data;\n"
      "  always_comb {hi, lo} = data;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->lhs, nullptr);
  EXPECT_EQ(item->body->lhs->kind, ExprKind::kConcatenation);
}

// ---------------------------------------------------------------------------
// 28. always_comb with nested ternary expressions
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_NestedTernary) {
  auto r = Parse(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic a, b, c, y;\n"
      "  always_comb y = sel[1] ? (sel[0] ? a : b) : c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->rhs, nullptr);
  EXPECT_EQ(item->body->rhs->kind, ExprKind::kTernary);
}

// ---------------------------------------------------------------------------
// 29. always_comb with unique if
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_UniqueIf) {
  auto r = Parse(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [3:0] out;\n"
      "  always_comb begin\n"
      "    unique if (sel == 2'b00)\n"
      "      out = 4'd0;\n"
      "    else if (sel == 2'b01)\n"
      "      out = 4'd1;\n"
      "    else if (sel == 2'b10)\n"
      "      out = 4'd2;\n"
      "    else\n"
      "      out = 4'd3;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstAlwaysCombStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
  EXPECT_NE(stmt->then_branch, nullptr);
  EXPECT_NE(stmt->else_branch, nullptr);
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

// ---------------------------------------------------------------------------
// 2. always @* parses with AlwaysKind::kAlways.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysStarAlwaysKind) {
  auto r = Parse(
      "module m;\n"
      "  always @* a = b & c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlways);
}

// ---------------------------------------------------------------------------
// 3. always_comb has empty sensitivity list.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysCombEmptySensitivity) {
  auto r = Parse(
      "module m;\n"
      "  always_comb y = a | b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->sensitivity.empty());
}

// ---------------------------------------------------------------------------
// 4. always @* also has empty sensitivity (star consumed at module level).
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysStarEmptySensitivity) {
  auto r = Parse(
      "module m;\n"
      "  always @* y = a | b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->sensitivity.empty());
}

// ---------------------------------------------------------------------------
// 5. always @(*) is equivalent to always @* -- same empty sensitivity.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysStarParenEquivalent) {
  auto r = Parse(
      "module m;\n"
      "  always @(*) y = a & b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlways);
  EXPECT_TRUE(item->sensitivity.empty());
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
// 7. always @* body is directly on item->body (no event control wrapper).
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysStarBodyDirectAssign) {
  auto r = Parse(
      "module m;\n"
      "  always @* x = a ^ b;\n"
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

// ---------------------------------------------------------------------------
// 9. always @* with begin-end block body.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysStarBeginEndBlock) {
  auto r = Parse(
      "module m;\n"
      "  always @* begin\n"
      "    x = a & b;\n"
      "    y = a | c;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlways);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_EQ(item->body->stmts.size(), 2u);
}

// ---------------------------------------------------------------------------
// 10. always @(*) with begin-end block body.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysStarParenBeginEndBlock) {
  auto r = Parse(
      "module m;\n"
      "  always @(*) begin\n"
      "    p = q & r;\n"
      "    s = q | t;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_EQ(item->body->stmts.size(), 2u);
}

// ---------------------------------------------------------------------------
// 11. Side-by-side always_comb and always @* in the same module.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_SideBySideBothForms) {
  auto r = Parse(
      "module m;\n"
      "  always_comb x = a & b;\n"
      "  always @* y = c | d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* first = NthAlwaysItem(r, 0);
  auto* second = NthAlwaysItem(r, 1);
  ASSERT_NE(first, nullptr);
  ASSERT_NE(second, nullptr);
  EXPECT_EQ(first->always_kind, AlwaysKind::kAlwaysComb);
  EXPECT_EQ(second->always_kind, AlwaysKind::kAlways);
}

// ---------------------------------------------------------------------------
// 12. Side-by-side: both have their own body statements.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_SideBySideBodiesExist) {
  auto r = Parse(
      "module m;\n"
      "  always_comb x = a;\n"
      "  always @* y = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* first = NthAlwaysItem(r, 0);
  auto* second = NthAlwaysItem(r, 1);
  ASSERT_NE(first, nullptr);
  ASSERT_NE(second, nullptr);
  ASSERT_NE(first->body, nullptr);
  ASSERT_NE(second->body, nullptr);
  EXPECT_EQ(first->body->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(second->body->kind, StmtKind::kBlockingAssign);
}

// ---------------------------------------------------------------------------
// 13. always_comb with if-else body.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysCombIfElse) {
  auto r = Parse(
      "module m;\n"
      "  always_comb\n"
      "    if (sel) y = a;\n"
      "    else y = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysComb);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kIf);
  EXPECT_NE(item->body->then_branch, nullptr);
  EXPECT_NE(item->body->else_branch, nullptr);
}

// ---------------------------------------------------------------------------
// 14. always @* with if-else body.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysStarIfElse) {
  auto r = Parse(
      "module m;\n"
      "  always @*\n"
      "    if (sel) y = a;\n"
      "    else y = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlways);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kIf);
  EXPECT_NE(item->body->then_branch, nullptr);
  EXPECT_NE(item->body->else_branch, nullptr);
}

// ---------------------------------------------------------------------------
// 15. always_comb with case statement.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysCombCaseStatement) {
  auto r = Parse(
      "module m;\n"
      "  always_comb\n"
      "    case (sel)\n"
      "      2'b00: y = 4'h0;\n"
      "      2'b01: y = 4'h1;\n"
      "      default: y = 4'hf;\n"
      "    endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysComb);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kCase);
  EXPECT_GE(item->body->case_items.size(), 3u);
}

// ---------------------------------------------------------------------------
// 16. always @* with case statement.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysStarCaseStatement) {
  auto r = Parse(
      "module m;\n"
      "  always @*\n"
      "    case (sel)\n"
      "      2'b00: y = 4'h0;\n"
      "      2'b01: y = 4'h1;\n"
      "      default: y = 4'hf;\n"
      "    endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlways);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kCase);
  EXPECT_GE(item->body->case_items.size(), 3u);
}

// ---------------------------------------------------------------------------
// 17. always_comb with complex combinational logic (nested ternary).
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysCombComplexLogic) {
  auto r = Parse(
      "module m;\n"
      "  logic [3:0] a, b, c, y;\n"
      "  always_comb y = (a > b) ? (a + c) : (b - c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysComb);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->rhs, nullptr);
  EXPECT_EQ(item->body->rhs->kind, ExprKind::kTernary);
}

// ---------------------------------------------------------------------------
// 18. always @* with complex combinational logic (nested ternary).
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysStarComplexLogic) {
  auto r = Parse(
      "module m;\n"
      "  logic [3:0] a, b, c, y;\n"
      "  always @* y = (a > b) ? (a + c) : (b - c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlways);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->rhs, nullptr);
  EXPECT_EQ(item->body->rhs->kind, ExprKind::kTernary);
}

}  // namespace
