#pragma once

#include <initializer_list>
#include <string_view>

#include "elaborator/rtlir.h"
#include "gtest/gtest.h"

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
