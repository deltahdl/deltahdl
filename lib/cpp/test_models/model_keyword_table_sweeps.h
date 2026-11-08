#pragma once

#include <cstddef>
#include <iterator>
#include <string>

#include "helpers_keyword_sweep_skips.h"
#include "model_keyword_tables.h"

struct KeywordTableSweep {
  const char* what;
  const char* const* words;
  size_t count;
  size_t expected_count;
  const char* earlier[2];
  bool (*skip)(const std::string&);
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
