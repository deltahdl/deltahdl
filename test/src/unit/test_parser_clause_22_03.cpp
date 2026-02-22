#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

static bool ParseOk(const std::string &src) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", src);
  Preprocessor preproc(mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

TEST(ParserSection22, ResetallDirective) {
  EXPECT_TRUE(ParseOk("`resetall\n"
                      "module t;\n"
                      "endmodule\n"));
}

TEST(ParserSection22, ResetallBeforeMultipleModules) {
  EXPECT_TRUE(ParseOk("`resetall\n"
                      "module m1;\n"
                      "endmodule\n"
                      "module m2;\n"
                      "endmodule\n"));
}
