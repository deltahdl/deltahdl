// §22.14.4: IEEE Std 1364-2001-noconfig keywords

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

TEST(Lexer, KeywordVersion_Noconfig_ExcludesConfigKeywords) {
  // "config" was added in 1364-2001 but excluded by noconfig.
  auto kw = LookupKeyword("config", KeywordVersion::kVer13642001Noconfig);
  EXPECT_FALSE(kw.has_value());
  // "generate" was also added in 1364-2001 and NOT excluded.
  auto gen = LookupKeyword("generate", KeywordVersion::kVer13642001Noconfig);
  EXPECT_TRUE(gen.has_value());
}

}  // namespace
