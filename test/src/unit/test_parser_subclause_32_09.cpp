#include <gtest/gtest.h>

#include <string>

#include "fixture_parser.h"

using namespace delta;

namespace {

// Syntax 32-1 writes $sdf_annotate as a statement, so each test wraps the call
// under test in an initial block and pulls the parsed call back out.
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

// The one required operand: a call naming only the SDF file.
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

// sdf_file is an expression, so it may be written as the name of a variable
// holding the file name rather than as a literal.
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

// All seven operands, each written out.
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

// Each operand after the first is optional on its own, so a call may skip over
// the ones it does not care about on its way to a later one.
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

// A trailing operand may simply be left off, so the shorter forms are calls in
// their own right rather than a longer call with empty slots.
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

// The first slot may be written empty on the way to a later operand. That is a
// call with no sdf_file, which the annotator rejects when it runs; the parser's
// part is to keep the empty slot rather than shift the operands along.
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

// A module_instance need not be a dotted path; a bare instance name is one of
// its ordinary forms.
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

// Array indices are permitted in a module_instance, so an indexed element of
// an instance array is kept as an indexed name rather than flattened away.
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

// A deeper hierarchical path, and an index part way along it, are both ordinary
// module_instance forms.
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

// The call is a statement, so it is terminated by a semicolon like any other.
// Dropping the semicolon is not a $sdf_annotate call.
TEST(SdfAnnotateSyntax, CallWithoutItsTerminatingSemicolonIsRejected) {
  EXPECT_FALSE(ParseOk(
      "module top;\n  initial $sdf_annotate(\"timing.sdf\")\nendmodule\n"));
}

// The operand list is parenthesized; an unclosed list is not a call.
TEST(SdfAnnotateSyntax, CallWithAnUnclosedOperandListIsRejected) {
  EXPECT_FALSE(ParseOk(
      "module top;\n  initial $sdf_annotate(\"timing.sdf\";\nendmodule\n"));
}

}  // namespace
