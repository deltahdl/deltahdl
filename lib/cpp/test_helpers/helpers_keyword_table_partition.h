#pragma once

#include <gtest/gtest.h>

#include <cstddef>
#include <initializer_list>
#include <string>

#include "model_keyword_table_sweeps.h"

// How many entries of `tables`, counted across every table, spell `word`. A
// word two of the tables both hold is counted once for each of them, which is
// what a check for a table covering another table's ground reads.
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
      const std::string kWord = table.words[i];
      EXPECT_EQ(CountWordInTables(tables, kWord), 1u)
          << kWord << " is counted twice";
    }
  }
}
