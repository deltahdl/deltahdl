// §23.2.2.2: ANSI style list of port declarations

#include <gtest/gtest.h>
#include <string>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- Test helpers ---
struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string& src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {

// --- data_type_or_implicit ---
// data_type | implicit_data_type
// --- implicit_data_type ---
// [signing] {packed_dimension}
TEST(ParserA221, ImplicitDataType) {
  // Implicit data type with just packed dimension
  auto r = Parse("module m(input [7:0] d); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_NE(port.data_type.packed_dim_left, nullptr);
}

TEST(ParserA221, ImplicitDataTypeSigned) {
  // signed [7:0]
  auto r = Parse("module m(input signed [7:0] d); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_TRUE(port.data_type.is_signed);
}

}  // namespace
