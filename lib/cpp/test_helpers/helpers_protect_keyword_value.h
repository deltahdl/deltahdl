#pragma once

#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"

using namespace delta;

// What a protect pragma keyword is left holding by a source, and what that
// reaches among the keys a tool was handed.
//
// §34.4 gives every one of those keywords a value that belongs to the position
// the reading has got to rather than to the directive that wrote it, so a case
// asking what a text put in effect asks it of a preprocessor that has finished
// reading rather than of the text it produced. The subclauses defining the
// keywords one at a time each want the same two questions asked, which is why
// the asking is written once here.

// A pragma_value written as the string a `<keyword> = <string>` subclause
// defines its expression with.
//
// §22.5.1 gives a pragma_value more than one spelling, and the quoted one is
// what those subclauses name. A case writing a value bare is making a claim
// about the other spelling and writes it without this.
inline std::string InQuotes(std::string_view value) {
  std::string text = "\"";
  text.append(value).append("\"");
  return text;
}

// A produced envelope up to and including the end_protected line §34.5.4.1
// closes it with.
//
// This tool writes a reset after that line, as the worked example in §34.3.1
// does, and §34.5.31.2 has the reset restore every protect pragma keyword to
// its default. A case asking what an envelope put in effect therefore asks it
// of the text the envelope governs and stops where the envelope does: past the
// reset every keyword reads back as defaulted whatever the envelope held, so
// the question would be answered the same way whether a block was opened or
// not. What the reset itself restores is read in
// test/src/unit/test_preprocessor_subclause_34_05_31_02.cpp.
inline std::string ThroughEndProtected(const std::string& envelope) {
  constexpr std::string_view kEnds = "`pragma protect end_protected\n";
  std::size_t at = envelope.rfind(kEnds);
  EXPECT_NE(at, std::string::npos) << envelope;
  if (at == std::string::npos) return envelope;
  return envelope.substr(0, at + kEnds.size());
}

// A reading of one source, with the preprocessor kept alive afterwards.
//
// The reading is given no keys. A tool that holds none reports nothing about a
// name reaching none of them -- §34.5.12, §34.5.18 and §34.5.25 each ask that
// only of a tool that knows the entity at all -- so a case built on this varies
// the spelling it writes and nothing else. Keys are handed to the question
// rather than to the reading, by KeyBlockKeyReached below.
struct ReadKeywordScope {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp{mgr, diag, PreprocConfig{}};
  // What the reading produced. A keyword defined as standing alone speaks for
  // the line beneath it, and what a case asks of such a keyword is whether that
  // line was taken as the value or left as text of the design, which is a
  // question about this rather than about the scope.
  std::string text;

  explicit ReadKeywordScope(const std::string& src) {
    text = pp.Preprocess(mgr.AddFile("<test>", src));
    EXPECT_FALSE(diag.HasErrors()) << src;
  }

  // The value in effect for `keyword` where the reading stopped, beside whether
  // a default put it there rather than a directive.
  ProtectKeywordValue ValueOf(std::string_view keyword) const {
    return pp.ProtectKeywords().ValueOf(keyword);
  }

  // The key §34.5.27 opens a region's key block with, reached out of `keys` by
  // the entity and the designation the reading left in effect.
  std::string_view KeyBlockKeyReached(const ProtectKeyList& keys) const {
    return ProtectKeyBlockKey(pp.ProtectKeywords(), keys);
  }
};
