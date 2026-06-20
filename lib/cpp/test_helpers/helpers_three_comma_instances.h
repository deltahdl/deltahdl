#pragma once

#include <gtest/gtest.h>

#include <string>

#include "fixture_parser.h"

using namespace delta;

// Parses a module body containing exactly three comma-separated instances and
// verifies that the first three module items are named u0, u1, and u2 in order.
inline void ExpectThreeCommaSeparatedInstances(const std::string& src) {
  auto r = Parse(src);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 3u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->inst_name, "u0");
  EXPECT_EQ(r.cu->modules[0]->items[1]->inst_name, "u1");
  EXPECT_EQ(r.cu->modules[0]->items[2]->inst_name, "u2");
}
