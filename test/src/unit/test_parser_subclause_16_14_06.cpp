#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

Stmt* FirstEmbeddedProceduralStmt(const ParseResult& result,
                                  ModuleItemKind block_kind) {
  if (result.has_errors || result.cu == nullptr || result.cu->modules.empty()) {
    return nullptr;
  }
  auto* mod = result.cu->modules.back();
  for (auto* it : mod->items) {
    if (it->kind != block_kind || it->body == nullptr) continue;
    auto* body = it->body;
    if (body->kind == StmtKind::kBlock) {
      return body->stmts.empty() ? nullptr : body->stmts.front();
    }
    return body;
  }
  return nullptr;
}

TEST(EmbeddedConcurrentAssertion, AssertPropertyEmbeddedInAlways) {
  EXPECT_TRUE(
      ParseOk("module m(input logic clk, input logic a);\n"
              "  always @(posedge clk) begin\n"
              "    assert property (a |-> a);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(EmbeddedConcurrentAssertion, CoverPropertyEmbeddedInAlways) {
  EXPECT_TRUE(
      ParseOk("module m(input logic clk, input logic a);\n"
              "  always @(posedge clk) begin\n"
              "    cover property (a);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(EmbeddedConcurrentAssertion, AstFlagsProceduralConcurrentAssertion) {
  auto result = Parse(
      "module m(input logic clk, input logic a);\n"
      "  always @(posedge clk) begin\n"
      "    assert property (a);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_FALSE(result.has_errors);
  ASSERT_NE(result.cu, nullptr);
  ASSERT_FALSE(result.cu->modules.empty());

  auto* mod = result.cu->modules.back();
  Stmt* found = nullptr;
  for (auto* it : mod->items) {
    if (it->kind == ModuleItemKind::kAlwaysBlock) {
      auto* body = it->body;
      ASSERT_NE(body, nullptr);
      if (body->kind == StmtKind::kBlock && !body->stmts.empty()) {
        found = body->stmts.front();
      } else if (body->kind == StmtKind::kAssertImmediate) {
        found = body;
      }
    }
  }
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->kind, StmtKind::kAssertImmediate);
  EXPECT_TRUE(found->is_procedural_concurrent);
  EXPECT_FALSE(found->is_deferred);
}

TEST(EmbeddedConcurrentAssertion, AssumePropertyEmbeddedInAlways) {
  auto result = Parse(
      "module m(input logic clk, input logic a);\n"
      "  always @(posedge clk) begin\n"
      "    assume property (a);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_FALSE(result.has_errors);
  auto* found =
      FirstEmbeddedProceduralStmt(result, ModuleItemKind::kAlwaysBlock);
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->kind, StmtKind::kAssumeImmediate);
  EXPECT_TRUE(found->is_procedural_concurrent);
  EXPECT_FALSE(found->is_deferred);
}

TEST(EmbeddedConcurrentAssertion, AssertPropertyEmbeddedInInitial) {
  auto result = Parse(
      "module m(input logic clk, input logic a);\n"
      "  initial begin\n"
      "    assert property (a |=> a);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_FALSE(result.has_errors);
  auto* found =
      FirstEmbeddedProceduralStmt(result, ModuleItemKind::kInitialBlock);
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->kind, StmtKind::kAssertImmediate);
  EXPECT_TRUE(found->is_procedural_concurrent);
}

TEST(EmbeddedConcurrentAssertion,
     ImmediateAssertNotFlaggedProceduralConcurrent) {
  auto result = Parse(
      "module m(input logic a);\n"
      "  always @(a) begin\n"
      "    assert (a);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_FALSE(result.has_errors);
  auto* found =
      FirstEmbeddedProceduralStmt(result, ModuleItemKind::kAlwaysBlock);
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->kind, StmtKind::kAssertImmediate);
  EXPECT_FALSE(found->is_procedural_concurrent);
}

TEST(EmbeddedConcurrentAssertion, ProceduralAssertKeepsItsBooleanProperty) {
  auto result = Parse(
      "module m(input logic clk, input logic a);\n"
      "  always @(posedge clk) assert property (a);\n"
      "endmodule\n");
  ASSERT_FALSE(result.has_errors);
  ASSERT_NE(result.cu, nullptr);
  ASSERT_FALSE(result.cu->modules.empty());
  auto* mod = result.cu->modules.back();
  Stmt* found = nullptr;
  for (auto* it : mod->items) {
    if (it->kind == ModuleItemKind::kAlwaysBlock) found = it->body;
  }
  ASSERT_NE(found, nullptr);
  EXPECT_TRUE(found->is_procedural_concurrent);
  ASSERT_NE(found->assert_expr, nullptr);
  EXPECT_EQ(found->assert_expr->kind, ExprKind::kIdentifier);
  EXPECT_EQ(found->assert_expr->text, "a");
  EXPECT_TRUE(found->is_concurrent_clocked);
}

TEST(EmbeddedConcurrentAssertion, ProceduralSpecIsReadAsAStaticOnes) {
  auto result = Parse(
      "module m(input logic clk, input logic a, input logic b);\n"
      "  always @(posedge clk) begin\n"
      "    assert property (a |-> b);\n"
      "    assert property (@(posedge b) a);\n"
      "    cover sequence (a ##1 b);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_FALSE(result.has_errors);
  EXPECT_TRUE(result.diags.empty());
  ASSERT_NE(result.cu, nullptr);
  ASSERT_FALSE(result.cu->modules.empty());
  auto* mod = result.cu->modules.back();
  Stmt* body = nullptr;
  for (auto* it : mod->items) {
    if (it->kind == ModuleItemKind::kAlwaysBlock) body = it->body;
  }
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->stmts.size(), 3u);
  const Stmt* temporal = body->stmts[0];
  EXPECT_TRUE(temporal->is_procedural_concurrent);
  EXPECT_TRUE(temporal->assert_clock.empty());
  ASSERT_NE(temporal->assert_property, nullptr);
  EXPECT_EQ(temporal->assert_property->kind,
            PropertyExprNode::Kind::kImplication);
  const Stmt* clocked = body->stmts[1];
  ASSERT_EQ(clocked->assert_clock.size(), 1u);
  EXPECT_EQ(clocked->assert_clock[0].edge, Edge::kPosedge);
  ASSERT_NE(clocked->assert_expr, nullptr);
  EXPECT_EQ(clocked->assert_expr->text, "a");
  const Stmt* sequence = body->stmts[2];
  EXPECT_EQ(sequence->kind, StmtKind::kCoverImmediate);
  EXPECT_TRUE(sequence->cover_sequence);
  EXPECT_NE(sequence->assert_sequence, nullptr);
}

TEST(EmbeddedConcurrentAssertion, ProceduralBooleanAssertIsNotReported) {
  auto result = Parse(
      "module m(input logic clk, input logic a);\n"
      "  always @(posedge clk) assert property (a);\n"
      "endmodule\n");
  EXPECT_FALSE(ReportedWarning(result.diags,
                               "procedural concurrent assertion is not "
                               "evaluated",
                               2, "16.14.6"));
}

}  // namespace
