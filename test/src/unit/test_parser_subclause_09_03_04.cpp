#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

TEST(SourceText, CheckerEndLabel) {
  auto r = Parse("checker chk; endchecker : chk\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ModuleAndHierarchyParsing, EndLabelInterface) {
  auto r = Parse("interface myif; endinterface : myif\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->interfaces.size(), 1);
  EXPECT_EQ(r.cu->interfaces[0]->name, "myif");
}

TEST(ModuleAndHierarchyParsing, EndLabelProgram) {
  auto r = Parse("program myprog; endprogram : myprog\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->programs.size(), 1);
  EXPECT_EQ(r.cu->programs[0]->name, "myprog");
}

TEST(BlockNames, MismatchedEndLabelIsError) {
  auto r = Parse("module foo; endmodule : bar\n");
  EXPECT_TRUE(ReportedError(r.diags, "end label 'bar' does not match 'foo'", 1,
                            "9.3.4"));
}

TEST(BlockNameParsing, LabeledSeqBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : my_block\n"
      "    a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  EXPECT_EQ(body->label, "my_block");
}

TEST(BlockNameParsing, LabeledSeqBlockWithMatchingEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : blk\n"
      "    a = 1;\n"
      "  end : blk\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->label, "blk");
}

TEST(BlockNameParsing, MismatchedEndLabelError) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : foo\n"
      "    a = 1;\n"
      "  end : bar\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags, "end label 'bar' does not match block name 'foo'", 4, "9.3.4"));
}

TEST(BlockNameParsing, NamedForkBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork : workers\n"
      "      a = 1;\n"
      "      b = 2;\n"
      "    join : workers\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->label, "workers");
}

TEST(BlockNameParsing, NamedForkWithBareJoinOmittingEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork : workers\n"
      "      a = 1;\n"
      "      b = 2;\n"
      "    join\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->label, "workers");
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoin);
}

TEST(BlockNameParsing, NamedForkMismatchedEndLabelError) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork : alpha\n"
      "      a = 1;\n"
      "    join : beta\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags,
                            "end label 'beta' does not match block name "
                            "'alpha'",
                            5, "9.3.4"));
}

TEST(BlockNameParsing, NamedForkWithJoinAnyLabel) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork : fg\n"
      "      a = 1;\n"
      "      b = 2;\n"
      "    join_any : fg\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->label, "fg");
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoinAny);
}

TEST(BlockNameParsing, NamedForkWithJoinNoneLabel) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork : bg\n"
      "      a = 1;\n"
      "    join_none : bg\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->label, "bg");
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoinNone);
}

TEST(BlockNameParsing, MismatchedJoinAnyEndLabelError) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork : x\n"
      "      a = 1;\n"
      "    join_any : y\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags, "end label 'y' does not match block name 'x'", 5, "9.3.4"));
}

TEST(BlockNameParsing, MismatchedJoinNoneEndLabelError) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork : x\n"
      "      a = 1;\n"
      "    join_none : y\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags, "end label 'y' does not match block name 'x'", 5, "9.3.4"));
}

TEST(BlockNameParsing, EndLabelOnUnnamedSeqBlockError) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "  end : orphan\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags, "end label 'orphan' specified for unnamed block", 4, "9.3.4"));
}

TEST(BlockNameParsing, JoinLabelOnUnnamedForkError) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 1;\n"
      "    join : orphan\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags, "end label 'orphan' specified for unnamed block", 5, "9.3.4"));
}

TEST(BlockNameParsing, NamedBlockWithVarDecl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : blk\n"
      "    int x;\n"
      "    x = 5;\n"
      "  end : blk\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->label, "blk");
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
}

TEST(BlockNameParsing, NestedNamedBlocks) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : outer\n"
      "    begin : inner\n"
      "      a = 1;\n"
      "    end : inner\n"
      "  end : outer\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->label, "outer");
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kBlock);
  EXPECT_EQ(body->stmts[0]->label, "inner");
}

TEST(BlockNameParsing, NamedEmptySeqBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : empty_blk\n"
      "  end : empty_blk\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->label, "empty_blk");
  EXPECT_EQ(body->stmts.size(), 0u);
}

TEST(BlockNameParsing, NamedEmptyForkBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork : empty_fork\n"
      "    join : empty_fork\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->label, "empty_fork");
  EXPECT_EQ(stmt->fork_stmts.size(), 0u);
}

struct ScopeWrap {
  const char* open;
  const char* close;
  uint32_t lines_before;
};

constexpr ScopeWrap kGenerateScopes[] = {
    {"module m;\n", "endmodule\n", 1},
    {"module m;\n  generate\n", "  endgenerate\nendmodule\n", 2},
    {"interface i;\n", "endinterface\n", 1},
    {"program p;\n", "endprogram\n", 1},
};

constexpr ScopeWrap kRoutineScopes[] = {
    {"module m;\n", "endmodule\n", 1},
    {"class c;\n", "endclass\n", 1},
    {"interface i;\n", "endinterface\n", 1},
    {"program p;\n", "endprogram\n", 1},
    {"package k;\n", "endpackage\n", 1},
    {"", "", 0},
};

std::string Wrapped(const ScopeWrap& w, std::string_view body) {
  return std::string(w.open) + std::string(body) + w.close;
}

std::string MismatchMessage(std::string_view label, std::string_view name) {
  return "end label '" + std::string(label) + "' does not match '" +
         std::string(name) + "'";
}

std::string BlockMismatchMessage(std::string_view label,
                                 std::string_view name) {
  return "end label '" + std::string(label) + "' does not match block name '" +
         std::string(name) + "'";
}

void ExpectReported(const std::string& src, const std::string& message,
                    uint32_t line) {
  auto r = Parse(src);
  EXPECT_TRUE(ReportedError(r.diags, message, line, "9.3.4")) << src;
}

void ExpectAccepted(const std::string& src) {
  auto r = Parse(src);
  EXPECT_NE(r.cu, nullptr) << src;
  EXPECT_FALSE(r.has_errors) << src;
}

template <size_t N>
void ExpectReportedInEach(const ScopeWrap (&scopes)[N], std::string_view body,
                          const std::string& message, uint32_t body_line) {
  for (const auto& w : scopes) {
    ExpectReported(Wrapped(w, body), message, w.lines_before + body_line);
  }
}

template <size_t N>
void ExpectAcceptedInEach(const ScopeWrap (&scopes)[N], std::string_view body) {
  for (const auto& w : scopes) ExpectAccepted(Wrapped(w, body));
}

TEST(GenerateBlockEndNames, AnElseBranchClosedByAnotherNameIsReported) {
  ExpectReportedInEach(kGenerateScopes,
                       "  if (0) begin : g\n"
                       "  end else begin : e\n"
                       "  end : f\n",
                       BlockMismatchMessage("f", "e"), 3);
  ExpectAcceptedInEach(kGenerateScopes,
                       "  if (0) begin : g\n"
                       "  end else begin : e\n"
                       "  end : e\n");
}

TEST(GenerateBlockEndNames, ACaseItemClosedByAnotherNameIsReported) {
  ExpectReportedInEach(kGenerateScopes,
                       "  case (1)\n"
                       "    1: begin : c\n"
                       "    end : d\n"
                       "  endcase\n",
                       BlockMismatchMessage("d", "c"), 3);
  ExpectAcceptedInEach(kGenerateScopes,
                       "  case (1)\n"
                       "    1: begin : c\n"
                       "    end : c\n"
                       "  endcase\n");
}

TEST(GenerateBlockEndNames, ALoopBlockClosedByAnotherNameIsReported) {
  ExpectReportedInEach(kGenerateScopes,
                       "  for (genvar i = 0; i < 2; i++) begin : g\n"
                       "  end : h\n",
                       BlockMismatchMessage("h", "g"), 2);
  ExpectAcceptedInEach(kGenerateScopes,
                       "  for (genvar i = 0; i < 2; i++) begin : g\n"
                       "  end : g\n");
}

TEST(GenerateBlockEndNames, ALabelledBlockClosedByAnotherNameIsReported) {
  ExpectReportedInEach(kGenerateScopes,
                       "  if (1) g : begin\n"
                       "  end : h\n",
                       BlockMismatchMessage("h", "g"), 2);
  ExpectAcceptedInEach(kGenerateScopes,
                       "  if (1) g : begin\n"
                       "  end : g\n");
}

TEST(GenerateBlockEndNames, AnInnerBlockClosedByTheOuterNameIsReported) {
  ExpectReportedInEach(kGenerateScopes,
                       "  if (1) begin : o\n"
                       "    if (1) begin : n\n"
                       "    end : o\n"
                       "  end : o\n",
                       BlockMismatchMessage("o", "n"), 3);
  ExpectAcceptedInEach(kGenerateScopes,
                       "  if (1) begin : o\n"
                       "    if (1) begin : n\n"
                       "    end : n\n"
                       "  end : o\n");
}

TEST(KeywordEndLabels, APackageClosedByAnotherNameIsReported) {
  ExpectReported("package bar; endpackage : baz\n",
                 MismatchMessage("baz", "bar"), 1);
  ExpectReported(
      "package foo; endpackage\n"
      "package bar; endpackage : foo\n",
      MismatchMessage("foo", "bar"), 2);
  ExpectAccepted("package bar; endpackage : bar\n");
}

TEST(KeywordEndLabels, AnInterfaceClosedByAnotherNameIsReported) {
  ExpectReported("interface simple_bus; endinterface : other_bus\n",
                 MismatchMessage("other_bus", "simple_bus"), 1);
  ExpectReported(
      "interface a; endinterface\n"
      "interface b; endinterface : a\n",
      MismatchMessage("a", "b"), 2);
}

TEST(KeywordEndLabels, AProgramClosedByAnotherNameIsReported) {
  ExpectReported("program p; endprogram : q\n", MismatchMessage("q", "p"), 1);
}

TEST(KeywordEndLabels, AConfigClosedByAnotherNameIsReported) {
  ExpectReported(
      "config cfg;\n"
      "  design lib.top;\n"
      "endconfig : other\n",
      MismatchMessage("other", "cfg"), 3);
  ExpectAccepted(
      "config cfg;\n"
      "  design lib.top;\n"
      "endconfig : cfg\n");
}

TEST(KeywordEndLabels, AClassClosedByAnotherNameIsReported) {
  ExpectReported("class C; endclass : D\n", MismatchMessage("D", "C"), 1);
  ExpectReported("interface class IC; endclass : JC\n",
                 MismatchMessage("JC", "IC"), 1);
  ExpectReported("class P #(int N = 1); endclass : Q\n",
                 MismatchMessage("Q", "P"), 1);
  ExpectReported(
      "class C; endclass\n"
      "virtual class V; endclass : C\n",
      MismatchMessage("C", "V"), 2);
  ExpectReported(
      "module m;\n"
      "  class C; endclass : D\n"
      "endmodule\n",
      MismatchMessage("D", "C"), 2);
  ExpectReported(
      "package k;\n"
      "  class C; endclass : D\n"
      "endpackage\n",
      MismatchMessage("D", "C"), 2);
  ExpectReported(
      "class O;\n"
      "  class C; endclass : D\n"
      "endclass\n",
      MismatchMessage("D", "C"), 2);
  ExpectAccepted("class C; endclass : C\n");
  ExpectAccepted("interface class IC; endclass : IC\n");
  ExpectAccepted("class P #(int N = 1); endclass : P\n");
}

TEST(KeywordEndLabels, ATaskClosedByAnotherNameIsReportedInEveryScope) {
  ExpectReportedInEach(kRoutineScopes, "  task t; endtask : u\n",
                       MismatchMessage("u", "t"), 1);
  ExpectAcceptedInEach(kRoutineScopes, "  task t; endtask : t\n");
}

TEST(KeywordEndLabels, AFunctionClosedByAnotherNameIsReportedInEveryScope) {
  ExpectReportedInEach(kRoutineScopes,
                       "  function int f; return 0; endfunction : g\n",
                       MismatchMessage("g", "f"), 1);
  ExpectAcceptedInEach(kRoutineScopes,
                       "  function int f; return 0; endfunction : f\n");
}

TEST(KeywordEndLabels, AnOutOfBlockMethodClosedByAnotherNameIsReported) {
  ExpectReported(
      "class C; extern function void f(); endclass\n"
      "function void C::f(); endfunction : g\n",
      MismatchMessage("g", "f"), 2);
  ExpectReported(
      "class C; extern function new(); endclass\n"
      "function C::new(); endfunction : f\n",
      MismatchMessage("f", "new"), 2);
  ExpectReported(
      "class C; extern task t(); endclass\n"
      "task C::t(); endtask : u\n",
      MismatchMessage("u", "t"), 2);
  ExpectAccepted(
      "class C; extern function void f(); endclass\n"
      "function void C::f(); endfunction : f\n");
  ExpectAccepted(
      "class C; extern function new(); endclass\n"
      "function C::new(); endfunction : new\n");
  ExpectAccepted(
      "class C; extern task t(); endclass\n"
      "task C::t(); endtask : t\n");
}

}  // namespace
