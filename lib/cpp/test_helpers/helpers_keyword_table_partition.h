#pragma once

#include <gtest/gtest.h>

#include <cstddef>
#include <initializer_list>
#include <string>

#include "model_keyword_table_sweeps.h"

// A version_specifier's reserved word list is exactly the tables §22.14 says
// that version names, put together. Both halves of that have to be checked: a
// per-table sweep passing for each table on its own leaves it open that the
// tables between them cover less of the list than the whole of it, or that one
// word is counted twice because two tables both hold it.
inline void ExpectTablesPartitionTheList(
    std::initializer_list<KeywordTableSweep> tables, size_t expected_total) {
  size_t total = 0;
  for (const auto& t : tables) total += t.count;
  EXPECT_EQ(total, expected_total);

  for (const auto& table : tables) {
    for (size_t i = 0; i < table.count; ++i) {
      const std::string word = table.words[i];
      size_t seen = 0;
      for (const auto& other : tables) {
        for (size_t j = 0; j < other.count; ++j) {
          if (word == other.words[j]) ++seen;
        }
      }
      EXPECT_EQ(seen, 1u) << word << " is counted twice";
    }
  }
}
