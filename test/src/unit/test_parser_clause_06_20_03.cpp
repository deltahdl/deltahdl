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

// =============================================================================
// Section 8.10 -- Type parameters
// =============================================================================
// Module with type parameter.
TEST(ParserSection8, TypeParameterModule) {
  EXPECT_TRUE(
      ParseOk("module m #(parameter type T = int);\n"
              "  T data;\n"
              "endmodule\n"));
}

// Module with type parameter defaulting to logic vector.
TEST(ParserSection8, TypeParameterLogicVector) {
  EXPECT_TRUE(
      ParseOk("module m #(parameter type T = logic [7:0]);\n"
              "  T bus;\n"
              "endmodule\n"));
}

TEST(ParserSection6, TypeParamDefaultLogicVector) {
  // §6.20.3: Type parameter with a vector default.
  EXPECT_TRUE(
      ParseOk("module m #(parameter type DATA_T = logic [15:0])\n"
              "  ();\n"
              "  DATA_T data;\n"
              "endmodule\n"));
}

// Step 1d: type parameter in module header (fixes 6.20.3)
TEST(ParserSection6, TypeParamPort) {
  EXPECT_TRUE(ParseOk6("module top #(type T = real); endmodule\n"));
}

// Step 1d: localparam type declaration (fixes 6.23-localparam_type_decl)
TEST(ParserSection6, LocalparamTypeDecl) {
  EXPECT_TRUE(
      ParseOk6("module t;\n"
               "  localparam type testtype = logic;\n"
               "  testtype x;\n"
               "endmodule\n"));
}

}  // namespace
