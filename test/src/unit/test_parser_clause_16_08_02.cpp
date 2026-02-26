// §16.8.2: Local variable formal arguments in sequence declarations

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

static bool ParseOk(const std::string& src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

  return nullptr;
}

namespace {

// =============================================================================
// §A.2.10 Productions #22-#23: sequence_port_list, sequence_port_item
// sequence_port_item ::=
//     { attribute_instance } [ local [ sequence_lvar_port_direction ] ]
//     sequence_formal_type formal_port_identifier { variable_dimension }
//     [ = sequence_actual_arg ]
// =============================================================================
TEST(ParserA210, SequencePortItem_LocalInout) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(local inout int x);\n"
              "    x > 0;\n"
              "  endsequence\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.10 Production #24: sequence_lvar_port_direction
// sequence_lvar_port_direction ::= input | inout | output
// =============================================================================
TEST(ParserA210, SequenceLvarPortDirection_Input) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(local input int x);\n"
              "    x;\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(ParserA210, SequenceLvarPortDirection_Output) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(local output int x);\n"
              "    (1, x = a) ##1 (1, x = b);\n"
              "  endsequence\n"
              "endmodule\n"));
}

}  // namespace
