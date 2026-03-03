// §8.26.2: Extends versus implements

#include "fixture_parser.h"

using namespace delta;

namespace {

// Class with implements clause.
TEST(SourceText, ClassWithImplements) {
  auto r = Parse("class C implements I; endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "C");
}

// Class implementing multiple interface classes.
TEST(ParserSection8, ClassImplementsMultipleInterfaces) {
  EXPECT_TRUE(
      ParseOk("interface class A;\n"
              "  pure virtual function void fa();\n"
              "endclass\n"
              "interface class B;\n"
              "  pure virtual function void fb();\n"
              "endclass\n"
              "class C implements A, B;\n"
              "  virtual function void fa();\n"
              "  endfunction\n"
              "  virtual function void fb();\n"
              "  endfunction\n"
              "endclass\n"));
}

struct ParseResult8b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult8b Parse(const std::string& src) {
  ParseResult8b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

// §8.26 — Class implements interface class
TEST(ParserSection8, ClassImplementsInterface) {
  auto r = Parse(
      "interface class PutIf;\n"
      "  pure virtual function void put(int a);\n"
      "endclass\n"
      "class Fifo implements PutIf;\n"
      "  virtual function void put(int a);\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  EXPECT_EQ(r.cu->classes[1]->name, "Fifo");
}

}  // namespace
