#pragma once

#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

struct GenerateBlockItem {
  std::string head;
  std::string decls;
  std::string item;
};

inline constexpr uint32_t kGenerateBlockItemLine = 4;

inline std::vector<std::string> InsideGenerateBlocks(
    const GenerateBlockItem& form) {
  const std::string kModule = form.head + "module m;\n";
  const std::string kTop = kModule + "  " + form.decls + "\n";
  return {
      kTop + "  if (1) begin : g\n    " + form.item + "\n  end\nendmodule\n",
      kTop +
          "  for (genvar i = 0; i < 2; i++) begin : g\n    if (1) begin : h " +
          form.item + " end\n  end\nendmodule\n",
      kTop + "  case (1)\n    0: begin : skipped end default: begin : g " +
          form.item + " end\n  endcase\nendmodule\n",
      kModule + "  if (1) begin : g\n    " + form.decls + "\n    " + form.item +
          "\n  end\nendmodule\n",
  };
}

inline ::testing::AssertionResult RejectedInsideGenerateBlocks(
    const GenerateBlockItem& form, std::string_view message,
    std::string_view subclause) {
  for (const std::string& src : InsideGenerateBlocks(form)) {
    ElabFixture f;
    ElaborateSrc(src, f);
    auto reported = ReportedError(f.diag.Diagnostics(), message,
                                  kGenerateBlockItemLine, subclause);
    if (!reported) return reported << "\nin\n" << src;
  }
  return ::testing::AssertionSuccess();
}

inline ::testing::AssertionResult AcceptedInsideGenerateBlocks(
    const GenerateBlockItem& form) {
  for (const std::string& src : InsideGenerateBlocks(form)) {
    if (!ElabOk(src)) {
      return ::testing::AssertionFailure() << "rejected\n" << src;
    }
  }
  return ::testing::AssertionSuccess();
}
