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

inline constexpr KeywordTableSweep kVerilog1995KeywordSweep = {
    "Table 22-1",
    kVerilog1995Keywords,
    std::size(kVerilog1995Keywords),
    102,
    {nullptr},
    IsGatePrimitiveWord,
    96};

// Table 22-1 at the parse stage, where nothing has to be skipped: the parser
// reads a declaration whose identifier slot holds a gate primitive word as a
// malformed gate instantiation and rejects it, which is the same verdict the
// sweep asks for, so all 102 entries are reached here.
inline constexpr KeywordTableSweep kVerilog1995KeywordSweepAtParse = {
    "Table 22-1",
    kVerilog1995Keywords,
    std::size(kVerilog1995Keywords),
    102,
    {nullptr},
    nullptr,
    102};

inline constexpr KeywordTableSweep kVerilog2001AddedKeywordSweep = {
    "Table 22-2",
    kVerilog2001AddedKeywords,
    std::size(kVerilog2001AddedKeywords),
    21,
    {"1364-1995"},
    nullptr,
    21};

inline constexpr KeywordTableSweep kVerilog2005AddedKeywordSweep = {
    "Table 22-3",
    kVerilog2005AddedKeywords,
    std::size(kVerilog2005AddedKeywords),
    1,
    {"1364-2001", "1364-1995"},
    nullptr,
    1};

inline constexpr KeywordTableSweep kSystemVerilog2005AddedKeywordSweep = {
    "Table 22-4",
    kSystemVerilog2005AddedKeywords,
    std::size(kSystemVerilog2005AddedKeywords),
    97,
    {"1364-2005"},
    IsAggregateOpenerWord,
    95};

inline constexpr KeywordTableSweep kSystemVerilog2009AddedKeywordSweep = {
    "Table 22-5",
    kSystemVerilog2009AddedKeywords,
    std::size(kSystemVerilog2009AddedKeywords),
    23,
    {"1800-2005"},
    nullptr,
    23};

inline constexpr KeywordTableSweep kSystemVerilog2012AddedKeywordSweep = {
    "Table 22-6",
    kSystemVerilog2012AddedKeywords,
    std::size(kSystemVerilog2012AddedKeywords),
    4,
    {"1800-2009"},
    nullptr,
    4};
