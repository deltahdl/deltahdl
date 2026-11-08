#pragma once

#include <gtest/gtest.h>

#include <string>

#include "common/diagnostic.h"
#include "fixture_elaborator.h"

using namespace delta;

inline void ExpectNoError(const std::string& src) {
  SCOPED_TRACE(src);
  ElabFixture f;
  ElaborateSrc(src, f);
  for (const Diagnostic& diag : f.diag.Diagnostics()) {
    if (diag.severity == DiagSeverity::kError)
      ADD_FAILURE() << "line " << diag.loc.line << ": " << diag.message;
  }
}
