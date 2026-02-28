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

}  // namespace
