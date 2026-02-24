// Annex A.2.1.2: Port declarations

#include <gtest/gtest.h>
#include <string>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

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

namespace {

// --- input_declaration ---
// input net_port_type list_of_port_identifiers
// | input variable_port_type list_of_variable_identifiers
TEST(ParserA212, InputNetPortType) {
  auto r = Parse("module m(input wire [7:0] d); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto &port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInput);
  EXPECT_NE(port.data_type.packed_dim_left, nullptr);
}

TEST(ParserA212, InputVariablePortTypeLogic) {
  auto r = Parse("module m(input logic [7:0] d); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto &port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInput);
}

}  // namespace
