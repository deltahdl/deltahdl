#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- Test helpers ---

struct ParseResult7c {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult7c Parse(const std::string& src) {
  ParseResult7c result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =============================================================================
// LRM section 7.4.5 -- Dynamic arrays
// =============================================================================

TEST(ParserSection7c, DynamicArrayDecl) {
  auto r = Parse(
      "module m;\n"
      "  int dyn[];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserSection7c, DynamicArrayNewConstruct) {
  auto r = Parse(
      "module m;\n"
      "  int dyn[];\n"
      "  initial dyn = new[10];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection7c, DynamicArrayNewWithInit) {
  auto r = Parse(
      "module m;\n"
      "  int dyn[];\n"
      "  int src[];\n"
      "  initial begin\n"
      "    src = new[5];\n"
      "    dyn = new[10](src);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection7c, DynamicArraySize) {
  auto r = Parse(
      "module m;\n"
      "  int dyn[];\n"
      "  int sz;\n"
      "  initial begin\n"
      "    dyn = new[5];\n"
      "    sz = dyn.size();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection7c, DynamicArrayDelete) {
  auto r = Parse(
      "module m;\n"
      "  int dyn[];\n"
      "  initial begin\n"
      "    dyn = new[5];\n"
      "    dyn.delete();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// LRM section 7.7 -- Queues
// =============================================================================

TEST(ParserSection7c, QueueDecl) {
  auto r = Parse(
      "module m;\n"
      "  int q[$];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection7c, QueueWithMaxSize) {
  auto r = Parse(
      "module m;\n"
      "  int q[$:255];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection7c, QueuePushBack) {
  auto r = Parse(
      "module m;\n"
      "  int q[$];\n"
      "  initial begin\n"
      "    q.push_back(42);\n"
      "    q.push_front(0);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection7c, QueuePopFront) {
  auto r = Parse(
      "module m;\n"
      "  int q[$];\n"
      "  int val;\n"
      "  initial begin\n"
      "    q.push_back(1);\n"
      "    val = q.pop_front();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection7c, QueueInsertAndDelete) {
  auto r = Parse(
      "module m;\n"
      "  int q[$];\n"
      "  initial begin\n"
      "    q.push_back(1);\n"
      "    q.push_back(3);\n"
      "    q.insert(1, 2);\n"
      "    q.delete(0);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection7c, QueueOfStrings) {
  auto r = Parse(
      "module m;\n"
      "  string names[$];\n"
      "  initial begin\n"
      "    names.push_back(\"hello\");\n"
      "    names.push_back(\"world\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}
