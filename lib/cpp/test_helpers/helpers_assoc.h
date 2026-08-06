#pragma once

#include <gtest/gtest.h>

#include <cstddef>
#include <initializer_list>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "fixture_simulator.h"
#include "parser/ast.h"

using namespace delta;

// Build a select expression  base_name[int_literal].
inline Expr* MakeAssocSelect(Arena& arena, int64_t idx_val,
                             std::string_view base_name = "aa") {
  auto* sel = arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  auto* base = arena.Create<Expr>();
  base->kind = ExprKind::kIdentifier;
  base->text = base_name;
  sel->base = base;
  auto* idx = arena.Create<Expr>();
  idx->kind = ExprKind::kIntegerLiteral;
  idx->int_val = idx_val;
  sel->index = idx;
  return sel;
}

// Elaborates and runs `src`, then checks the keys the string-indexed
// associative array `name` holds against `expected`, in the order the array
// stores them.
//
// A string-indexed array orders its keys lexicographically however the source
// inserted them, so a test states the insertion order in the source and reads
// the whole key sequence back as the verdict.
inline void RunAndExpectStringKeys(
    const char* src, std::string_view name,
    std::initializer_list<const char*> expected) {
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* aa = f.ctx.FindAssocArray(name);
  ASSERT_NE(aa, nullptr);
  std::vector<std::string> keys;
  for (const auto& [key, val] : aa->str_data) keys.push_back(key);
  ASSERT_EQ(keys.size(), expected.size());
  size_t i = 0;
  for (const char* want : expected) {
    EXPECT_EQ(keys[i], want) << i;
    ++i;
  }
}
