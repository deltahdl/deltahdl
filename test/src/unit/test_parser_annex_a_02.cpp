#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

namespace {

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

} // namespace

// =============================================================================
// A.2 -- Overview tests
// =============================================================================

TEST(ParserAnnexA, A2NetDeclWire) {
  auto r = Parse("module m; wire [3:0] w; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kNetDecl);
}

TEST(ParserAnnexA, A2NetDeclTriWandWor) {
  auto r = Parse("module m; tri t; wand wa; wor wo; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items.size(), 3u);
}

TEST(ParserAnnexA, A2VarDeclWithInit) {
  auto r = Parse("module m; logic [7:0] data = 8'hFF; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_NE(r.cu->modules[0]->items[0]->init_expr, nullptr);
}

TEST(ParserAnnexA, A2ParamDecl) {
  auto r = Parse("module m;\n"
                 "  parameter int WIDTH = 16;\n"
                 "  localparam int DEPTH = 32;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(r.cu->modules[0]->items[1]->kind, ModuleItemKind::kParamDecl);
}

TEST(ParserAnnexA, A2TypedefEnumWithBase) {
  auto r = Parse("module m;\n"
                 "  typedef enum logic [1:0] {IDLE, RUN, DONE} state_t;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kTypedef);
}

TEST(ParserAnnexA, A2TypedefStructPacked) {
  auto r = Parse("module m;\n"
                 "  typedef struct packed {\n"
                 "    logic [7:0] addr;\n"
                 "    logic [31:0] data;\n"
                 "  } req_t;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kTypedef);
}

TEST(ParserAnnexA, A2FunctionDeclAutomaticParse) {
  auto r = Parse("module m;\n"
                 "  function automatic int add(int a, int b);\n"
                 "    return a + b;\n"
                 "  endfunction\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(item->name, "add");
}

TEST(ParserAnnexA, A2FunctionDeclAutomaticProps) {
  auto r = Parse("module m;\n"
                 "  function automatic int add(int a, int b);\n"
                 "    return a + b;\n"
                 "  endfunction\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->is_automatic);
  EXPECT_EQ(item->func_args.size(), 2u);
}

TEST(ParserAnnexA, A2TaskDecl) {
  auto r = Parse("module m;\n"
                 "  task automatic drive(input logic [7:0] val);\n"
                 "    data = val;\n"
                 "  endtask\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_EQ(item->name, "drive");
}

TEST(ParserAnnexA, A2ClassDecl) {
  auto r = Parse("class Packet;\n"
                 "  rand bit [7:0] payload;\n"
                 "  function void display();\n"
                 "    $display(\"pkt\");\n"
                 "  endfunction\n"
                 "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "Packet");
  EXPECT_EQ(r.cu->classes[0]->members.size(), 2u);
}

TEST(ParserAnnexA, A2ClassWithConstraint) {
  auto r = Parse("class C;\n"
                 "  rand int x;\n"
                 "  constraint c1 { x > 0; x < 100; }\n"
                 "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserAnnexA, A2CovergroupDecl) {
  auto r = Parse("module m;\n"
                 "  covergroup cg @(posedge clk);\n"
                 "    coverpoint x;\n"
                 "  endgroup\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserAnnexA, A2ContinuousAssignWithDelay) {
  auto r = Parse("module m; wire y; assign #5 y = a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      EXPECT_NE(item->assign_delay, nullptr);
    }
  }
}
