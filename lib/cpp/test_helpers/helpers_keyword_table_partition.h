#pragma once

#include <gtest/gtest.h>

#include <cstddef>
#include <initializer_list>
#include <string>

#include "model_keyword_table_sweeps.h"

inline size_t CountWordInTables(std::initializer_list<KeywordTableSweep> tables,
                                const std::string& word) {
  size_t seen = 0;
  for (const auto& table : tables) {
    for (size_t i = 0; i < table.count; ++i) {
      if (word == table.words[i]) ++seen;
    }
  }
  return seen;
}

inline void ExpectTablesPartitionTheList(
    std::initializer_list<KeywordTableSweep> tables, size_t expected_total) {
  size_t total = 0;
  for (const auto& t : tables) total += t.count;
  EXPECT_EQ(total, expected_total);

  for (const auto& table : tables) {
    for (size_t i = 0; i < table.count; ++i) {
      const std::string kWord = table.words[i];
      EXPECT_EQ(CountWordInTables(tables, kWord), 1u)
          << kWord << " is counted twice";
    }
  }
}
