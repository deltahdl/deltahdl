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

// Opens a `begin_keywords region for `spec` around `body` and closes it again.
// The region comes from real directives rather than a fixture setting, which
// is the point: §22.14 makes the directive the thing that puts a version's
// reserved word list in force for the source that follows it.
inline std::string In(const char* spec, const std::string& body) {
  return std::string("`begin_keywords \"") + spec + "\"\n" + body +
         "`end_keywords\n";
}

// The nine version_specifiers §22.14 admits, each naming the reserved word
// list that version defines: Table 22-1 for 1364-1995, and each later list
// including the ones before it.
inline std::string In1995(const std::string& body) {
  return In("1364-1995", body);
}
inline std::string In2001(const std::string& body) {
  return In("1364-2001", body);
}
// 1364-2001-noconfig is 1364-2001 less the ten configuration words, the one
// specifier whose list is smaller than its neighbour's.
inline std::string InNoconfig(const std::string& body) {
  return In("1364-2001-noconfig", body);
}
inline std::string In2005(const std::string& body) {
  return In("1364-2005", body);
}
// 1800-2005 is the first SystemVerilog version_specifier.
inline std::string InSv2005(const std::string& body) {
  return In("1800-2005", body);
}
inline std::string InSv2009(const std::string& body) {
  return In("1800-2009", body);
}
inline std::string InSv2012(const std::string& body) {
  return In("1800-2012", body);
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

// The same, for a specifier string that may not name any version at all. The
// diagnostics are read but not asserted on -- whether an unrecognized string
// is an error is settled elsewhere; what matters here is only which reserved
// word list the source that follows ends up being read under.
inline TokenKind KindAfterSpecifier(const std::string& spec,
                                    const std::string& word) {
  PreprocFixture f;
  auto out = Preprocess(
      "`begin_keywords \"" + spec + "\"\n" + word + "\n`end_keywords\n", f);

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
