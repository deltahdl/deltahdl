#pragma once

#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast.h"

using namespace delta;

// Verify that a successfully parsed module contains exactly one item of each of
// the five concurrent assertion kinds: assert, assume, cover property, cover
// sequence, and restrict property.
inline void VerifyAllFiveConcurrentAssertionTypes(ParseResult& r) {
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssertProperty),
      nullptr);
  ASSERT_NE(
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssumeProperty),
      nullptr);
  ASSERT_NE(
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverProperty),
      nullptr);
  ASSERT_NE(
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverSequence),
      nullptr);
  ASSERT_NE(FindItemByKind(r.cu->modules[0]->items,
                           ModuleItemKind::kRestrictProperty),
            nullptr);
}
