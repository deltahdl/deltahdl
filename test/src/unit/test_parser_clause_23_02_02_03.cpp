// §23.2.2.3: Rules for determining port kind, data type, and direction

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

TEST(ParserA212, InoutImplicitType) {
  auto r = Parse("module m(inout a); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kInout);
}

// --- interface_port_declaration ---
// interface_identifier list_of_interface_identifiers
// | interface_identifier . modport_identifier list_of_interface_identifiers
// Note: Interface ports without direction keyword in ANSI port lists are
// lexically ambiguous with non-ANSI identifier-only port lists. The parser
// treats identifier-only port lists as non-ANSI; semantic analysis resolves
// interface types. This tests the non-ANSI parsing path.
TEST(ParserA212, InterfacePortParsedAsNonAnsi) {
  // Without direction keyword, interface ports parse as non-ANSI port names.
  auto r = Parse("module m(a); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "a");
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kNone);
}

}  // namespace
