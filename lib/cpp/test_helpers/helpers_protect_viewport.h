#pragma once

#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_diagnosed.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_viewport.h"

using namespace delta;

inline std::string ProtectDirective(std::string_view expressions) {
  std::string text = "`pragma protect ";
  text.append(expressions).append("\n");
  return text;
}

inline std::string ViewportOf(std::string_view object,
                              std::string_view access) {
  std::string expression = "viewport = ( object = \"";
  expression.append(object).append("\" , access = \"");
  expression.append(access).append("\" )");
  return ProtectDirective(expression);
}

struct ReadingViewports {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Diagnosed diagnosed{diag};
  Preprocessor pp{mgr, diag, PreprocConfig{}};
  std::string text;

  explicit ReadingViewports(const std::string& src) {
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  const std::vector<ProtectViewport>& Viewports() const {
    return pp.ProtectViewports();
  }

  size_t Count() const { return pp.ProtectViewports().size(); }
};
