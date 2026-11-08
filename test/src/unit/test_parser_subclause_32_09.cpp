#include <gtest/gtest.h>

#include <cstddef>
#include <string>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

const Expr* SdfCall(const ParseResult& r) {
  if (r.cu == nullptr || r.cu->modules.empty()) return nullptr;
  for (auto* item : r.cu->modules.back()->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    const Stmt* body = item->body;
    if (body == nullptr) return nullptr;
    if (body->kind == StmtKind::kBlock && !body->stmts.empty()) {
      body = body->stmts[0];
    }
    return body->expr;
  }
  return nullptr;
}

ParseResult ParseSdfAnnotate(const std::string& args) {
  return Parse("module top;\n  initial $sdf_annotate(" + args +
               ");\nendmodule\n");
}

TEST(SdfAnnotateSyntax, SdfFileAloneIsAWholeCall) {
  ParseResult r = ParseSdfAnnotate("\"timing.sdf\"");
  EXPECT_FALSE(r.has_errors);
  const Expr* call = SdfCall(r);
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(call->kind, ExprKind::kSystemCall);
  EXPECT_EQ(call->callee, "$sdf_annotate");
  ASSERT_EQ(call->args.size(), 1u);
  ASSERT_NE(call->args[0], nullptr);
  EXPECT_EQ(call->args[0]->kind, ExprKind::kStringLiteral);
}

TEST(SdfAnnotateSyntax, SdfFileMayBeWrittenAsAnExpression) {
  ParseResult r = Parse(
      "module top;\n  string f = \"timing.sdf\";\n"
      "  initial $sdf_annotate(f);\nendmodule\n");
  EXPECT_FALSE(r.has_errors);
  const Expr* call = SdfCall(r);
  ASSERT_NE(call, nullptr);
  ASSERT_EQ(call->args.size(), 1u);
  ASSERT_NE(call->args[0], nullptr);
  EXPECT_EQ(call->args[0]->kind, ExprKind::kIdentifier);
}

TEST(SdfAnnotateSyntax, EveryOperandMayBeSupplied) {
  ParseResult r = ParseSdfAnnotate(
      "\"timing.sdf\", top.dut, \"cfg.txt\", \"ann.log\", \"MAXIMUM\", "
      "\"1.6:1.4:1.2\", \"FROM_MTM\"");
  EXPECT_FALSE(r.has_errors);
  const Expr* call = SdfCall(r);
  ASSERT_NE(call, nullptr);
  ASSERT_EQ(call->args.size(), 7u);
  for (const auto* arg : call->args) EXPECT_NE(arg, nullptr);
  EXPECT_EQ(call->args[1]->kind, ExprKind::kMemberAccess);
  EXPECT_EQ(call->args[4]->text, "\"MAXIMUM\"");
  EXPECT_EQ(call->args[6]->text, "\"FROM_MTM\"");
}

TEST(SdfAnnotateSyntax, OperandsSkippedOnTheWayToALaterOneAreEmptySlots) {
  ParseResult r = ParseSdfAnnotate("\"timing.sdf\", , , , \"MINIMUM\"");
  EXPECT_FALSE(r.has_errors);
  const Expr* call = SdfCall(r);
  ASSERT_NE(call, nullptr);
  ASSERT_EQ(call->args.size(), 5u);
  EXPECT_NE(call->args[0], nullptr);
  EXPECT_EQ(call->args[1], nullptr);
  EXPECT_EQ(call->args[2], nullptr);
  EXPECT_EQ(call->args[3], nullptr);
  ASSERT_NE(call->args[4], nullptr);
  EXPECT_EQ(call->args[4]->text, "\"MINIMUM\"");
}

TEST(SdfAnnotateSyntax, TrailingOperandsMayBeLeftOff) {
  for (int count = 1; count <= 7; ++count) {
    std::string args = "\"timing.sdf\"";
    const char* const kRest[] = {"top.dut",         "\"cfg.txt\"",
                                 "\"a.log\"",       "\"TYPICAL\"",
                                 "\"1.0:1.0:1.0\"", "\"FROM_MTM\""};
    for (int i = 0; i + 1 < count; ++i) {
      args += ", ";
      args += kRest[i];
    }
    ParseResult r = ParseSdfAnnotate(args);
    EXPECT_FALSE(r.has_errors) << "operand count " << count;
    const Expr* call = SdfCall(r);
    ASSERT_NE(call, nullptr) << "operand count " << count;
    EXPECT_EQ(call->args.size(), static_cast<size_t>(count));
  }
}

TEST(SdfAnnotateSyntax, SdfFileSlotMayBeWrittenEmpty) {
  ParseResult r = ParseSdfAnnotate(", top.dut");
  EXPECT_FALSE(r.has_errors);
  const Expr* call = SdfCall(r);
  ASSERT_NE(call, nullptr);
  ASSERT_EQ(call->args.size(), 2u);
  EXPECT_EQ(call->args[0], nullptr);
  ASSERT_NE(call->args[1], nullptr);
  EXPECT_EQ(call->args[1]->kind, ExprKind::kMemberAccess);
}

TEST(SdfAnnotateSyntax, ModuleInstanceMayBeABareInstanceName) {
  ParseResult r = ParseSdfAnnotate("\"timing.sdf\", dut");
  EXPECT_FALSE(r.has_errors);
  const Expr* call = SdfCall(r);
  ASSERT_NE(call, nullptr);
  ASSERT_EQ(call->args.size(), 2u);
  ASSERT_NE(call->args[1], nullptr);
  EXPECT_EQ(call->args[1]->kind, ExprKind::kIdentifier);
  EXPECT_EQ(call->args[1]->text, "dut");
}

TEST(SdfAnnotateSyntax, ModuleInstanceMayCarryArrayIndices) {
  ParseResult r = ParseSdfAnnotate("\"timing.sdf\", top.bank[1]");
  EXPECT_FALSE(r.has_errors);
  const Expr* call = SdfCall(r);
  ASSERT_NE(call, nullptr);
  ASSERT_EQ(call->args.size(), 2u);
  ASSERT_NE(call->args[1], nullptr);
  EXPECT_EQ(call->args[1]->kind, ExprKind::kSelect);
  ASSERT_NE(call->args[1]->base, nullptr);
  EXPECT_EQ(call->args[1]->base->kind, ExprKind::kMemberAccess);
  ASSERT_NE(call->args[1]->index, nullptr);
}

TEST(SdfAnnotateSyntax, ModuleInstanceMayIndexPartWayAlongAPath) {
  ParseResult r = ParseSdfAnnotate("\"timing.sdf\", top.bank[2].core");
  EXPECT_FALSE(r.has_errors);
  const Expr* call = SdfCall(r);
  ASSERT_NE(call, nullptr);
  ASSERT_EQ(call->args.size(), 2u);
  ASSERT_NE(call->args[1], nullptr);
  EXPECT_EQ(call->args[1]->kind, ExprKind::kMemberAccess);
  ASSERT_NE(call->args[1]->lhs, nullptr);
  EXPECT_EQ(call->args[1]->lhs->kind, ExprKind::kSelect);
}

TEST(SdfAnnotateSyntax, CallWithoutItsTerminatingSemicolonIsRejected) {
  ParseResult r = Parse(
      "module top;\n  initial $sdf_annotate(\"timing.sdf\")\nendmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endmodule'", 3, "12.3"));
}

TEST(SdfAnnotateSyntax, CallWithAnUnclosedOperandListIsRejected) {
  ParseResult r = Parse(
      "module top;\n  initial $sdf_annotate(\"timing.sdf\";\nendmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ')', got ';'", 2, "13.5"));
}

}  // namespace
