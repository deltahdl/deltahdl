#pragma once

#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_viewport.h"

using namespace delta;

// What a source text left an envelope describing, and what the reading
// reported about it.
//
// §34.5.32.2 has a viewport expression describe objects of the envelope in
// force rather than say anything about the text a reading produces, so a case
// asking what a text described asks it of a preprocessor that is still inside
// that envelope. The reading's reports are read off the same object, both
// subclauses of §34.5.32 having cases whose whole claim is which rule was
// reported.

// A protect pragma directive writing `expressions`, spelled as they stand here.
inline std::string ProtectDirective(std::string_view expressions) {
  std::string text = "`pragma protect ";
  text.append(expressions).append("\n");
  return text;
}

// The value §34.5.32.1 spells, naming `object` and asking `access` for it.
inline std::string ViewportOf(std::string_view object,
                              std::string_view access) {
  std::string expression = "viewport = ( object = \"";
  expression.append(object).append("\" , access = \"");
  expression.append(access).append("\" )");
  return ProtectDirective(expression);
}

// A reading of one source with the preprocessor kept alive afterwards.
//
// The envelope is left open by every source a case builds on this, because the
// expression closing one takes away what it described: what a case reads back
// is therefore read while the envelope that describes it still stands.
struct ReadingViewports {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp{mgr, diag, PreprocConfig{}};
  std::string text;

  explicit ReadingViewports(const std::string& src) {
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  // The objects the envelope in force was described by, in writing order.
  const std::vector<ProtectViewport>& Viewports() const {
    return pp.ProtectViewports();
  }

  // How many of them there are, which is what a case about one expression
  // checks before reading the expression back.
  size_t Count() const { return pp.ProtectViewports().size(); }
};
