// §6.20.3: Type parameters

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

// parameter_port_list: type parameter (#(type T = int))
TEST(SourceText, ParamPortTypeParameter) {
  auto r = Parse("module m #(type T = int); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->params.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->params[0].first, "T");
}

TEST(ParserA24, TypeAssignmentNoDefault) {
  auto r = Parse("module m #(parameter type T); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA24, TypeAssignmentComplexType) {
  auto r = Parse("module m; parameter type T = logic [7:0]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
