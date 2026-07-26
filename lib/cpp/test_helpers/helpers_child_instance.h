#pragma once

#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <initializer_list>
#include <string_view>

#include "elaborator/rtlir.h"

using namespace delta;

// Readbacks off the one instance a design's top module contains.
//
// A rule about what an instantiation does to the module it instantiates is
// stated over a design of exactly two modules -- the top, and the one child it
// instantiates -- so the elaborated child is reached by position rather than
// by name, and what elaboration settled on inside it is read from there.

// The module the design's sole top-level instance resolved to, or nullptr when
// the design holds no top module or that top module instantiates nothing.
inline RtlirModule* SoleChildInstance(RtlirDesign* design) {
  if (design == nullptr || design->top_modules.empty()) return nullptr;
  auto* top = design->top_modules[0];
  if (top->children.empty()) return nullptr;
  return top->children[0].resolved;
}

// One parameter as elaboration left it: the name it was declared under and the
// value it resolved to.
struct ResolvedParam {
  std::string_view name;
  int64_t value;
};

// Checks the parameters `mod` carries against `expected`, in declaration
// order: how many there are, the name each was declared under, and the value
// elaboration settled on. A parameter whose value depends on another one is
// checked here alongside the parameter it depends on, since the two are the
// same claim read at two points of one chain.
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

// Checks the width elaboration gave `mod`'s variable `name`. A variable
// declared with a parameterized type is the observable a type parameter's
// value produces, so the width it ended up with is what a test about that
// parameter reads.
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

// Checks that `mod`'s parameter `name` resolved to `value`, and that the value
// came from an override rather than from the parameter's own declaration.
//
// An override reaches a parameter from outside the module that declares it, so
// a test about one reads back both the value and the fact that it displaced
// the declared default.
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
