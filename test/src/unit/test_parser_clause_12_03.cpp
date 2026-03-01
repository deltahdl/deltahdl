// §12.3: Syntax

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

TEST(ParserA602, InitialConstruct_NullStmt) {
  // initial with null statement (just a semicolon)
  auto r = Parse(
      "module m;\n"
      "  initial ;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kInitialBlock);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kNull);
}

static Stmt* InitialBody(ParseResult& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    return item->body;
  }
  return nullptr;
}

// =============================================================================
// A.6.4 Statements
// =============================================================================
// ---------------------------------------------------------------------------
// statement_or_null ::= statement | { attribute_instance } ;
// ---------------------------------------------------------------------------
// §12.3: null statement (just semicolon)
TEST(ParserA604, NullStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kNull);
}

// §12.3: null statement with attribute instance
TEST(ParserA604, NullStatementWithAttribute) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    (* synthesis *) ;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  auto* stmt = body->stmts[0];
  EXPECT_EQ(stmt->kind, StmtKind::kNull);
  EXPECT_FALSE(stmt->attrs.empty());
  EXPECT_EQ(stmt->attrs[0].name, "synthesis");
}

// §12.3: multiple null statements
TEST(ParserA604, MultipleNullStatements) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ;\n"
      "    ;\n"
      "    ;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 3u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kNull);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kNull);
  EXPECT_EQ(body->stmts[2]->kind, StmtKind::kNull);
}

// §12.3: statement with attribute instance
TEST(ParserA604, StatementWithAttribute) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    (* full_case *) a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_FALSE(stmt->attrs.empty());
  EXPECT_EQ(stmt->attrs[0].name, "full_case");
}

// §12.3: statement with label AND attribute
TEST(ParserA604, StatementWithLabelAndAttribute) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    lbl: (* mark *) a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->label, "lbl");
  EXPECT_FALSE(stmt->attrs.empty());
  EXPECT_EQ(stmt->attrs[0].name, "mark");
}

}  // namespace
