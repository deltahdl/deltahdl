// §22.14.2: IEEE Std 1364-1995 keywords

#include <gtest/gtest.h>
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/keywords.h"
#include "lexer/lexer.h"

using namespace delta;

static std::vector<Token> Lex(const std::string &src) {
  static SourceManager mgr;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  return lexer.LexAll();
}

namespace {

TEST(Lexer, KeywordVersion_1364_1995_ModuleIsKeyword) {
  auto kw = LookupKeyword("module", KeywordVersion::kVer13641995);
  EXPECT_EQ(kw, std::optional(TokenKind::kKwModule));
}

}  // namespace
