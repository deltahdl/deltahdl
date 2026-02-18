#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// =========================================================================
// Section 5.11: Array literals
// =========================================================================

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

TEST(ParserCh511, ArrayLiteral_Nested) {
  // int n[1:2][1:3] = '{'{0,1,2},'{3{4}}};
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int n[1:2][1:3] = '{'{0,1,2},'{3{4}}};\n"
              "endmodule"));
}

TEST(ParserCh511, ArrayLiteral_Simple) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int arr[0:2] = '{10, 20, 30};\n"
              "endmodule"));
}

TEST(ParserCh511, ArrayLiteral_DefaultValue) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int arr[0:3] = '{default:0};\n"
              "endmodule"));
}
