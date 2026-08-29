#pragma once

#include <gtest/gtest.h>

#include <cstddef>
#include <ios>
#include <string>
#include <vector>

#include "helpers_text_lines.h"
#include "model_vcd_token_grammar.h"

// The form rules §21.7.2 and §21.7.4 both state about the dump file they
// define: it is free format -- one command per unit of white space, never two
// commands run together -- it is ASCII text throughout, and its three parts
// appear in creation order. Each holds of either file because the extended one
// inherits the 4-state command vocabulary by name equivalence, so the checks
// live here rather than once per subclause.

// Every declaration keyword a header and its definitions carry stands apart as
// its own token, and nothing in the file fuses two commands. `var_count` is
// how many objects the run defined, which is the one count that is exact --
// the rest may repeat.
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

// Every simulation-time command is a '#' immediately followed by decimal
// digits and nothing else, so a time never has another command run onto it.
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

// The file's three parts appear in creation order: header information first,
// then the variable or node definitions, then the value changes. That is the
// layout Figure 21-1 draws for the 4-state file and Figure 21-2 for the
// extended one. `var_line` is the definition the source's one dumped scalar
// produces, whose position separates the header from the definitions.
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
  EXPECT_LT(p_date, p_timescale);   // header information...
  EXPECT_LT(p_timescale, p_var);    // ...precedes the definitions...
  EXPECT_LT(p_var, p_defs_end);     // ...closed by $enddefinitions...
  EXPECT_LT(p_defs_end, p_change);  // ...and value changes come last
}

// Every byte of the file is ASCII text: a printable character, or one of the
// three white-space characters a free-format file may use to separate its
// commands. A 4-state value reaches the file as a letter rather than as a bit
// pattern, so nothing in it is outside that range.
inline void ExpectFileIsAsciiText(const std::string& content) {
  for (unsigned char c : content) {
    bool ascii_text =
        (c >= 0x20 && c < 0x7F) || c == '\n' || c == '\t' || c == '\r';
    ASSERT_TRUE(ascii_text) << "non-ASCII byte 0x" << std::hex << int{c};
  }
}
