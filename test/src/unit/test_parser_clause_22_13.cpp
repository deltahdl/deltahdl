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

// ============================================================================
// LRM section 22.13 -- `__FILE__ and `__LINE__
// ============================================================================

TEST(ParserSection22, FileDirectiveInDisplay) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $display(\"File: %s\", `__FILE__);\n"
              "endmodule\n"));
}

TEST(ParserSection22, LineDirectiveInDisplay) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $display(\"Line: %0d\", `__LINE__);\n"
              "endmodule\n"));
}

TEST(ParserSection22, FileAndLineInErrorMessage) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $display(\"Error at %s, line %d.\",\n"
              "    `__FILE__, `__LINE__);\n"
              "endmodule\n"));
}

TEST(ParserSection22, LineDirectiveInAssignment) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer line_num;\n"
              "  initial line_num = `__LINE__;\n"
              "endmodule\n"));
}

TEST(ParserSection22, FileDirectiveInStringConcat) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $display(\"source: %s:%0d\", `__FILE__, `__LINE__);\n"
              "endmodule\n"));
}
