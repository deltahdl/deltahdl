#pragma once

#include <gtest/gtest.h>

#include <string>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "lexer/lexer.h"

using namespace delta;

// Preprocesses a single token wrapped in a `begin_keywords/`end_keywords
// block for the given keyword version, lexes the preprocessed output, locates
// the token by its text, and asserts that it lexes with the expected kind.
inline void ExpectBeginKeywordsTokenKind(const std::string& version,
                                         const std::string& token_text,
                                         TokenKind expected_kind) {
  PreprocFixture f;
  auto out = Preprocess("`begin_keywords \"" + version + "\"\n" + token_text +
                            "\n`end_keywords\n",
                        f);
  EXPECT_FALSE(f.diag.HasErrors());

  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", out);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  auto tokens = lexer.LexAll();

  bool found = false;
  for (const auto& tok : tokens) {
    if (tok.text == token_text) {
      EXPECT_EQ(tok.kind, expected_kind);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}
