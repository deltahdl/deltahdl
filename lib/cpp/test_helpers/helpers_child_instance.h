#pragma once

#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <initializer_list>
#include <string_view>

#include "elaborator/rtlir.h"

using namespace delta;

inline RtlirModule* SoleChildInstance(RtlirDesign* design) {
  if (design == nullptr || design->top_modules.empty()) return nullptr;
  auto* top = design->top_modules[0];
  if (top->children.empty()) return nullptr;
  return top->children[0].resolved;
}

struct ResolvedParam {
  std::string_view name;
  int64_t value;
};

inline void ExpectResolvedParams(
    const RtlirModule* mod, std::initializer_list<ResolvedParam> expected) {
  ASSERT_NE(mod, nullptr);
  ASSERT_EQ(mod->params.size(), expected.size());
  size_t i = 0;
  for (const auto& want : expected) {
    EXPECT_EQ(mod->params[i].name, want.name);
    EXPECT_EQ(mod->params[i].resolved_value, want.value) << want.name;
    ++i;
  }
}

inline void ExpectVariableWidth(const RtlirModule* mod, std::string_view name,
                                uint32_t width) {
  ASSERT_NE(mod, nullptr);
  const RtlirVariable* found = nullptr;
  for (const auto& v : mod->variables) {
    if (v.name == name) found = &v;
  }
  ASSERT_NE(found, nullptr) << name;
  EXPECT_EQ(found->width, width);
}

inline void ExpectParamOverridden(const RtlirModule* mod, std::string_view name,
                                  int64_t value) {
  ASSERT_NE(mod, nullptr);
  bool found = false;
  for (const auto& p : mod->params) {
    if (p.name != name) continue;
    found = true;
    EXPECT_TRUE(p.is_resolved);
    EXPECT_TRUE(p.from_override);
    EXPECT_EQ(p.resolved_value, value);
  }
  EXPECT_TRUE(found) << name;
}
