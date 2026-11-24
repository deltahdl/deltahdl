#pragma once

#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

inline size_t ProtectDirectiveAt(std::string_view text, std::string_view name,
                                 size_t from = 0) {
  std::string directive = "`pragma protect ";
  directive.append(name);
  for (size_t at = text.find(directive, from); at != std::string_view::npos;
       at = text.find(directive, at + 1)) {
    size_t after = at + directive.size();
    if (after < text.size() && (text[after] == '=' || text[after] == '\n')) {
      return at;
    }
  }
  return std::string_view::npos;
}

inline size_t ProtectDirectiveCount(std::string_view text,
                                    std::string_view name) {
  size_t count = 0;
  for (size_t at = ProtectDirectiveAt(text, name); at != std::string_view::npos;
       at = ProtectDirectiveAt(text, name, at + 1)) {
    ++count;
  }
  return count;
}

inline ::testing::AssertionResult ProtectDirectivesInOrder(
    std::string_view text, const std::vector<std::string_view>& names) {
  size_t last = 0;
  for (std::string_view name : names) {
    size_t at = ProtectDirectiveAt(text, name);
    if (at == std::string_view::npos || at < last) {
      return ::testing::AssertionFailure()
             << name << " is missing or out of order in\n"
             << text;
    }
    last = at;
  }
  return ::testing::AssertionSuccess();
}

inline std::string ProtectBlockBeneath(std::string_view text,
                                       std::string_view name, size_t from = 0) {
  size_t at = ProtectDirectiveAt(text, name, from);
  if (at == std::string_view::npos) return "";
  size_t start = text.find('\n', at) + 1;
  size_t close = text.find("\n`pragma", start);
  if (close == std::string_view::npos) close = text.size();
  return std::string(text.substr(start, close - start));
}

inline ::testing::AssertionResult TextsInOrder(
    std::string_view text, const std::vector<std::string_view>& pieces) {
  size_t from = 0;
  for (std::string_view piece : pieces) {
    size_t at = text.find(piece, from);
    if (at == std::string_view::npos) {
      return ::testing::AssertionFailure()
             << piece << " is missing or out of order in\n"
             << text;
    }
    from = at + piece.size();
  }
  return ::testing::AssertionSuccess();
}

inline std::string WithTwoProtectBlocks(std::string_view names,
                                        std::string_view first,
                                        std::string_view second) {
  std::string src = "module m;\n";
  src.append(names);
  src.append("`pragma protect begin\n").append(first);
  src.append("`pragma protect end\n  wire between;\n");
  src.append("`pragma protect begin\n").append(second);
  src.append("`pragma protect end\nendmodule\n");
  return src;
}

inline ::testing::AssertionResult HoldsTwoRegionsAroundTheCleartext(
    std::string_view written) {
  if (ProtectDirectiveCount(written, "begin_protected") != 2) {
    return ::testing::AssertionFailure() << written;
  }
  return TextsInOrder(written,
                      {"module m;\n", "`pragma protect begin_protected\n",
                       "`pragma protect end_protected\n", "  wire between;\n",
                       "`pragma protect begin_protected\n",
                       "`pragma protect end_protected\n", "endmodule\n"});
}
