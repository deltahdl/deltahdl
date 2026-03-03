// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

struct ParseResult6 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult6 Parse(const std::string& src) {
  ParseResult6 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

namespace {

// =========================================================================
// §6.24.3 -- Bit-stream casting
// =========================================================================
TEST(ParserSection6, BitStreamCastToType) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { logic [3:0] a; logic [3:0] b; } pair_t;\n"
      "  initial begin\n"
      "    pair_t p;\n"
      "    p = pair_t'(8'hAB);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection6, BitStreamCastFromStruct) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { logic [3:0] a; logic [3:0] b; } pair_t;\n"
      "  initial begin\n"
      "    pair_t p;\n"
      "    logic [7:0] flat;\n"
      "    flat = logic [7:0]'(p);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection6, BitStreamCastStreaming) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    byte a;\n"
      "    int b;\n"
      "    b = int'({<< byte {a}});\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

// =========================================================================
// §6.15: Class
// =========================================================================
TEST(ParserSection6, ClassVarDecl_ClassParsed) {
  // Class declared at top-level, then used as a type inside a module.
  auto r = Parse(
      "class MyClass;\n"
      "  int x;\n"
      "endclass\n"
      "module t;\n"
      "  MyClass obj;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.cu->classes.empty());
  EXPECT_EQ(r.cu->classes[0]->name, "MyClass");
  ASSERT_FALSE(r.cu->modules.empty());
}

}  // namespace
