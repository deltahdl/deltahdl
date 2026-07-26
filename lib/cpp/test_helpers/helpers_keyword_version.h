#pragma once

#include <gtest/gtest.h>

#include <string>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "lexer/keywords.h"
#include "lexer/lexer.h"
#include "lexer/token.h"

// Source builders for the §22.14 `begin_keywords tests. Each wraps a body in
// the version_specifier whose reserved-word table the test is about, so the
// test states the version once and reads as the rule it checks.

// Wraps `body` in a real `begin_keywords "1364-1995" region, so the reserved
// word list Table 22-1 gives is the one in force while the design is built.
inline std::string In1995(const std::string& body) {
  return "`begin_keywords \"1364-1995\"\n" + body + "`end_keywords\n";
}

// Wraps `body` in a real `begin_keywords "1364-2001" region, so the reserved
// word list this version names is the one in force while the design is built.
inline std::string In2001(const std::string& body) {
  return "`begin_keywords \"1364-2001\"\n" + body + "`end_keywords\n";
}

// Wraps `body` in a real `begin_keywords "1364-2005" region, so the reserved
// word list this version names is the one in force while the design is built.
inline std::string In2005(const std::string& body) {
  return "`begin_keywords \"1364-2005\"\n" + body + "`end_keywords\n";
}

// Wraps `body` in a real `begin_keywords "1800-2005" region -- the first
// SystemVerilog version_specifier -- so the reserved word list this version
// names is the one in force while the design is built.
inline std::string InSv2005(const std::string& body) {
  return "`begin_keywords \"1800-2005\"\n" + body + "`end_keywords\n";
}

// A one-variable module declaring `word` as its variable name. A word the
// version in force reserves cannot be a declaration name, so this source
// elaborates exactly when the word is still an identifier there.
inline std::string VarDecl(const char* word) {
  return std::string("module m;\n  reg [7:0] ") + word + ";\nendmodule\n";
}

// Runs one word through a real `begin_keywords region for `version and reports
// the kind it lexes with. Going through the directive rather than calling the
// keyword table straight is the point: it is the region the directive opens
// that puts the version's list in force for the source that follows.
inline TokenKind KindInRegion(const std::string& version,
                              const std::string& word) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"" + version + "\"\n" + word + "\n`end_keywords\n", f);
  EXPECT_FALSE(f.diag.HasErrors()) << version << " / " << word;

  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", out);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  for (const auto& tok : lexer.LexAll()) {
    if (tok.text == word) return tok.kind;
  }
  ADD_FAILURE() << word << " never reached the token stream";
  return TokenKind::kError;
}
