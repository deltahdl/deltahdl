#pragma once

#include <cstddef>
#include <iterator>
#include <string>

#include "helpers_keyword_sweep_skips.h"
#include "model_keyword_tables.h"

// §22.14 names one reserved word list per version_specifier, and builds each
// out of the tables of Clause 22: the version's own table plus every table the
// versions before it introduced. The descriptions here are those tables, one
// constant apiece, so a check that sweeps a table and a check that adds the
// tables up work from the same account of what each one holds.

// One of §22.14's reserved word tables, described so a sweep can be driven
// from it.
struct KeywordTableSweep {
  // The table's name, which travels with every failure message.
  const char* what;
  const char* const* words;
  // Entries the model holds, and the entry count the table has in the
  // standard. The two are compared, so a model that drifts from the printed
  // table is reported rather than silently narrowing the sweep.
  size_t count;
  size_t expected_count;
  // Specifiers under which the table's words are still ordinary identifiers --
  // the lists this table's own version is built on. Table 22-1 has none: no
  // list precedes it, so its accepting leg is that its words still do their
  // keyword jobs, which the declaration checks carry instead.
  const char* earlier[2];
  // Entries a sweep cannot drive through the elaborator, and null when every
  // entry can be. helpers_keyword_sweep_skips.h says which stage carries them.
  bool (*skip)(const std::string&);
  // Entries a full sweep therefore reaches, so a skip predicate that started
  // matching more than it was written for is reported.
  size_t expected_swept;
};

inline constexpr KeywordTableSweep kSweepTable221 = {
    "Table 22-1",        kTable221, std::size(kTable221), 102, {nullptr},
    IsGatePrimitiveWord, 96};

inline constexpr KeywordTableSweep kSweepTable222 = {"Table 22-2",
                                                     kTable222Words,
                                                     std::size(kTable222Words),
                                                     21,
                                                     {"1364-1995"},
                                                     nullptr,
                                                     21};

inline constexpr KeywordTableSweep kSweepTable223 = {"Table 22-3",
                                                     kTable223,
                                                     std::size(kTable223),
                                                     1,
                                                     {"1364-2001", "1364-1995"},
                                                     nullptr,
                                                     1};

inline constexpr KeywordTableSweep kSweepTable224 = {"Table 22-4",
                                                     kTable224Words,
                                                     std::size(kTable224Words),
                                                     97,
                                                     {"1364-2005"},
                                                     IsAggregateOpenerWord,
                                                     95};

inline constexpr KeywordTableSweep kSweepTable225 = {"Table 22-5",
                                                     kTable225Words,
                                                     std::size(kTable225Words),
                                                     23,
                                                     {"1800-2005"},
                                                     nullptr,
                                                     23};

inline constexpr KeywordTableSweep kSweepTable226 = {"Table 22-6",
                                                     kTable226Words,
                                                     std::size(kTable226Words),
                                                     4,
                                                     {"1800-2009"},
                                                     nullptr,
                                                     4};
