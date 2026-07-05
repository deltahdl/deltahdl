#include "fixture_parser.h"

using namespace delta;

namespace {

// Returns the first assertion-like statement embedded directly in a procedural
// block of the given kind (kAlwaysBlock or kInitialBlock) in the last parsed
// module, or nullptr when there is none.
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

// §16.14.6: an `assume property` written inside a procedural block is a
// procedural concurrent assertion just like `assert`/`cover property`; the
// parser records it with the same is_procedural_concurrent flag. Covers the
// assume input form of the embedding rule.
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

// §16.14.6: the head names an initial procedure, alongside an always procedure,
// as a place a concurrent assertion can be embedded. An assert property in an
// initial block is flagged as a procedural concurrent assertion the same way.
// Covers the initial-block syntactic position of the embedding rule.
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

// §16.14.6 contrast/negative: an immediate assertion (no `property` keyword) in
// procedural code is NOT a procedural concurrent assertion. The parser must
// tell the two forms apart, leaving is_procedural_concurrent clear for the
// immediate assert so it is never queued as a pending procedural instance.
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

}  // namespace
