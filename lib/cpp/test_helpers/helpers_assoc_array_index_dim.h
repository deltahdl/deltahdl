#pragma once

#include <string>

#include "fixture_parser.h"

using namespace delta;

// Parses `src`, expects a clean parse, then locates the unpacked variable
// declaration named `var_name` and asserts its single unpacked dimension is an
// identifier expression whose text equals `expected_index_text` (the
// associative-array index type name).
inline void ExpectAssocArrayIdentifierIndexDim(
    const std::string& src, const std::string& var_name,
    const std::string& expected_index_text) {
  auto r = Parse(src);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto& items = r.cu->modules[0]->items;
  ModuleItem* var_item = nullptr;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kVarDecl && item->name == var_name) {
      var_item = item;
      break;
    }
  }
  ASSERT_NE(var_item, nullptr);
  ASSERT_EQ(var_item->unpacked_dims.size(), 1u);
  ASSERT_NE(var_item->unpacked_dims[0], nullptr);
  EXPECT_EQ(var_item->unpacked_dims[0]->kind, ExprKind::kIdentifier);
  EXPECT_EQ(var_item->unpacked_dims[0]->text, expected_index_text);
}
