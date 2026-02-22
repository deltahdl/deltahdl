#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

// §5.3 White space

using namespace delta;

static bool ParseOk(const std::string &src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

TEST(ParserCh503, BlockCommentSpanningLines) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  /* this comment\n"
              "     spans multiple\n"
              "     lines */\n"
              "  logic a;\n"
              "endmodule\n"));
}

TEST(ParserCh503, OneLineCommentEndsAtNewline) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic a; // comment\n"
              "  logic b;\n"
              "endmodule\n"));
}
