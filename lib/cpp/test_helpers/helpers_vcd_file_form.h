#pragma once

#include <gtest/gtest.h>

#include <cstddef>
#include <ios>
#include <string>
#include <vector>

#include "helpers_text_lines.h"
#include "model_vcd_token_grammar.h"

inline void ExpectDeclarationCommandsStandApart(
    const std::vector<std::string>& toks, size_t var_count) {
  ASSERT_FALSE(toks.empty());
  EXPECT_GE(CountToken(toks, "$date"), 1u);
  EXPECT_GE(CountToken(toks, "$version"), 1u);
  EXPECT_GE(CountToken(toks, "$timescale"), 1u);
  EXPECT_GE(CountToken(toks, "$scope"), 1u);
  EXPECT_EQ(CountToken(toks, "$var"), var_count);
  EXPECT_GE(CountToken(toks, "$upscope"), 1u);
  EXPECT_EQ(CountToken(toks, "$enddefinitions"), 1u);
  EXPECT_GE(CountToken(toks, "$end"), 1u);
  EXPECT_TRUE(NoFusedCommands(toks));
}

inline void ExpectSimulationTimesAreBareDecimals(
    const std::vector<std::string>& toks) {
  for (const auto& t : toks) {
    if (t[0] != '#') continue;
    ASSERT_GT(t.size(), 1u) << "bare # token";
    for (size_t i = 1; i < t.size(); ++i) {
      ASSERT_TRUE(t[i] >= '0' && t[i] <= '9')
          << "simulation time fused with another command: " << t;
    }
  }
}

inline void ExpectHeaderThenDefinitionsThenValueChanges(
    const std::string& content, const std::string& var_line,
    const std::string& first_change_time) {
  auto p_date = content.find("$date");
  auto p_timescale = content.find("$timescale");
  auto p_var = content.find(var_line);
  auto p_defs_end = content.find("$enddefinitions");
  auto p_change = content.find(first_change_time);
  ASSERT_NE(p_date, std::string::npos);
  ASSERT_NE(p_timescale, std::string::npos);
  ASSERT_NE(p_var, std::string::npos);
  ASSERT_NE(p_defs_end, std::string::npos);
  ASSERT_NE(p_change, std::string::npos);
  EXPECT_LT(p_date, p_timescale);
  EXPECT_LT(p_timescale, p_var);
  EXPECT_LT(p_var, p_defs_end);
  EXPECT_LT(p_defs_end, p_change);
}

inline void ExpectFileIsAsciiText(const std::string& content) {
  for (unsigned char c : content) {
    bool ascii_text =
        (c >= 0x20 && c < 0x7F) || c == '\n' || c == '\t' || c == '\r';
    ASSERT_TRUE(ascii_text) << "non-ASCII byte 0x" << std::hex << int{c};
  }
}
