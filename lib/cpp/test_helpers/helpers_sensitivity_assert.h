#pragma once

#include <initializer_list>
#include <string_view>

#include "elaborator/rtlir.h"
#include "gtest/gtest.h"

// Assertions over a process's inferred sensitivity list, for a §9.2.2.2.1 case
// that names the signals it expects to find or to be absent rather than walking
// RtlirProcess::sensitivity itself. The list is a vector of EventExpr and the
// order it holds is not something the clause fixes, so each of these searches
// it by name and neither asserts a position nor a count.
//
// Both are needed by any case that reads a process back, whichever half of the
// §9.2.2.2.1 cases it belongs to, which is why they are here rather than in a
// test source: the two halves are separate translation units, and a copy in
// each is what `copy-paste-test` in .github/workflows/deltahdl.yml reports.

using namespace delta;

inline void ExpectSensitivityContains(
    const RtlirProcess& proc,
    std::initializer_list<std::string_view> expected) {
  for (const auto& name : expected) {
    bool found = false;
    for (const auto& ev : proc.sensitivity) {
      if (ev.signal && ev.signal->text == name) {
        found = true;
        break;
      }
    }
    EXPECT_TRUE(found) << "missing sensitivity signal: " << name;
  }
}

inline void ExpectSensitivityExcludes(
    const RtlirProcess& proc,
    std::initializer_list<std::string_view> excluded) {
  for (const auto& name : excluded) {
    bool found = false;
    for (const auto& ev : proc.sensitivity) {
      if (ev.signal && ev.signal->text == name) {
        found = true;
        break;
      }
    }
    EXPECT_FALSE(found) << "unexpected sensitivity signal: " << name;
  }
}
